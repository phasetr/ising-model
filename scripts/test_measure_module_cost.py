#!/usr/bin/env python3
"""Tests for ``scripts/measure_module_cost.py``.

Run directly (``python3 scripts/test_measure_module_cost.py``) or through the
harness's own ``--self-test`` flag.

No ``lean``, no ``lake`` and no ``elan``: the timed child is either stubbed out
in Python or replaced by a small stub executable that prints a canned profiler
report, so nothing here compiles anything and the suite is safe to run while a
build holds the machine. It is not instantaneous -- the stub-executable cases
sleep a few tenths of a second on purpose, so that a reported ``import`` is
below the wall clock the harness measures around them -- and it shells out to
``git ls-files`` once to find the committed artifacts. Expect a few seconds.

What is worth testing in a stopwatch
------------------------------------
Not the clock. The value of this harness is that the *protocol* it encodes
cannot quietly drift, so the tests pin the properties whose loss would make two
runs incomparable while every printed number still looks plausible:

1. **A duration it cannot parse must fail, not become zero.** A silently zeroed
   ``import`` reads as a spectacular improvement and is indistinguishable, in
   the artifact, from a real one.
2. **The profiler report must be read from stderr.** Lean writes the whole
   report there; a stdout-only reader records no import figure at all. This is
   not hypothetical: it made this harness's own first run produce 24 measured
   samples and no valid one. That run's artifact was never committed -- a
   failed run is not a record worth publishing -- so the episode is
   development history, not something a reader can check from the tree.
3. **An impossible timing must be rejected.** ``import`` is a subinterval of
   the process ``real`` was measured around, so a child claiming more is not a
   slow module.
4. **Warm-up samples must stay out of the statistics and inside the record**,
   and a failed warm-up must fail the run. Counting warm-up samples
   re-introduces the cold-page-cache inflation that produced the historical
   7.0 s figure; dropping them from the JSON removes the evidence that the
   warm-up happened at all.
5. **The target set must be exactly what was asked for.** A glob that matches
   nothing, or a path that is missing, must stop the run rather than shrink a
   "family" to whatever happened to exist.
6. **An artifact must not be silently replaced**, and a committed artifact must
   be a complete, fully valid record.

The mutation cases follow the idiom of ``scripts/test_audit_gate.py``: a
fixture with a known verdict, and a :func:`load_mutated` re-import with one
surgical weakening applied, which the assertions must *lose* the property
under. A mutation whose target stops matching raises, so it cannot become
vacuous after the code moves. Where a property is about the harness's output,
the assertion is made against the artifact the harness writes -- never against
a filter the test re-implements, which would pass whatever the harness did.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import platform
import stat
import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import audit_gate  # noqa: E402
import measure_module_cost as mmc  # noqa: E402

SCRIPT_PATH = Path(mmc.__file__).resolve()

# A verbatim ``lean -Dprofiler=true`` report, captured from
# ``IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityH.lean``
# on 2026-07-31 (Lean 4.29.0). Kept literal so the parser is pinned against real
# compiler output, including the phase names that contain spaces and the mixed
# ``s``/``ms`` units. Lean prints all of this on **stderr** (stdout is empty for
# a clean module), which is why the harness parses the union of both streams --
# a stdout-only reader sees nothing at all.
PROFILER_STDOUT = """import took 1.6s
cumulative profiling times:
\tattribute application 0.00733ms
\telaboration 36.8ms
\tfix level params 0.0725ms
\timport 1.6s
\tinitialization 20.9ms
\tinstantiate metavars 0.00671ms
\tinterpretation 795ms
\tlet-to-have transformation 0.358ms
\tlinting 11.4ms
\tparsing 2.93ms
\tprocess pre-definitions 1.97ms
\tshare common exprs 0.0622ms
\ttype checking 0.68ms
\ttypeclass inference 6.99ms
"""

# Same shape, scaled down: a stub child returns in tens of milliseconds, so the
# report it prints must name an import a real process of that length could have
# had. ``0.2s`` against the stub's ``sleep`` of :data:`STUB_SLEEP_S`.
STUB_IMPORT_S = 0.2
STUB_SLEEP_S = 0.3
STUB_REPORT = (
    f"import took {STUB_IMPORT_S}s\n"
    "cumulative profiling times:\n"
    f"\timport {STUB_IMPORT_S}s\n"
    "\telaboration 36.8ms\n"
)

# Two real library modules, used wherever a run needs a target set that exists.
TWO_MODULES = (
    "IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularity.lean",
    "IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularityH.lean",
)


def load_mutated(*substitutions: tuple[str, str]) -> types.ModuleType:
    """Return ``measure_module_cost`` re-imported with textual weakenings applied.

    Each substitution must match exactly once; a target that stopped matching
    means the code moved and the mutation test using it is vacuous, so this
    raises rather than applying nothing. ``__file__`` keeps pointing at the real
    script so ``REPO_ROOT`` and friends resolve as in production.
    """
    source = SCRIPT_PATH.read_text(encoding="utf-8")
    for old, new in substitutions:
        count = source.count(old)
        if count != 1:
            raise AssertionError(f"mutation target matched {count} times, expected 1: {old!r}")
        source = source.replace(old, new)
    module = types.ModuleType("measure_module_cost_mutant")
    module.__file__ = str(SCRIPT_PATH)
    exec(compile(source, str(SCRIPT_PATH), "exec"), module.__dict__)  # noqa: S102
    return module


def fresh_module() -> types.ModuleType:
    """Return an unmutated re-import, safe to monkeypatch.

    Patching an attribute of the imported ``measure_module_cost`` would not take
    effect -- its functions resolve globals in the *original* module dict, so a
    stub installed on a shallow copy is simply not seen. Re-executing the source
    into a private module gives the stub the same visibility a real edit has.
    """
    return load_mutated()


def write_stub_lean(
    directory: Path,
    *,
    report: str = STUB_REPORT,
    stream: str = "stderr",
    sleep_s: float = 0.0,
    exit_code: int = 0,
    argv_out: Path | None = None,
) -> Path:
    """Write an executable stand-in for ``lean`` and return its path.

    The stub is what makes the stream question testable at all: it prints
    ``report`` on ``stream`` only, so a reader of the other stream observes
    exactly what a real ``lean`` would give it -- nothing. ``sleep_s`` sets a
    floor under the wall clock the harness measures, so a stub may report an
    import without reporting an impossible one; ``argv_out`` records the argv
    the harness actually spawned.
    """
    stub = directory / "lean_stub.py"
    stub.write_text(
        "#!/usr/bin/env python3\n"
        "import json, sys, time\n"
        f"argv_out = {None if argv_out is None else str(argv_out)!r}\n"
        "if argv_out is not None:\n"
        "    open(argv_out, 'w').write(json.dumps(sys.argv))\n"
        f"time.sleep({sleep_s!r})\n"
        f"sys.{stream}.write({report!r})\n"
        f"sys.exit({exit_code})\n",
        encoding="utf-8",
    )
    stub.chmod(stub.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return stub


def run_cli(module: types.ModuleType, argv: list[str]) -> tuple[int, str, str]:
    """Run ``module.main(argv)``, capturing its streams; return code, out, err."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = module.main(argv)
    return code, out.getvalue(), err.getvalue()


def sample(module: str, phase: str, real: float, import_s: float | None, valid: bool = True):
    """Return a minimal sample record shaped like :func:`measure_module_cost.measure_once`."""
    return {
        "module": module,
        "phase": phase,
        "real": real,
        "user": real / 2,
        "sys": real / 4,
        "import": import_s,
        "own": None if import_s is None else real - import_s,
        "valid": valid,
        "problems": [] if valid else ["stub failure"],
    }


class DurationTest(unittest.TestCase):
    """Duration parsing: every unit Lean emits, and hard failure on the rest."""

    def test_units(self) -> None:
        """Seconds, milliseconds, microseconds (both spellings) and nanoseconds."""
        self.assertAlmostEqual(mmc.parse_duration("1.6s"), 1.6)
        self.assertAlmostEqual(mmc.parse_duration("14s"), 14.0)
        self.assertAlmostEqual(mmc.parse_duration("36.8ms"), 0.0368)
        self.assertAlmostEqual(mmc.parse_duration("0.00733ms"), 7.33e-6)
        self.assertAlmostEqual(mmc.parse_duration("12us"), 1.2e-5)
        self.assertAlmostEqual(mmc.parse_duration("12µs"), 1.2e-5)
        self.assertAlmostEqual(mmc.parse_duration("500ns"), 5e-7)

    def test_ms_is_not_read_as_s(self) -> None:
        """``ms`` must win over ``s``: the reverse understates import by 1000x."""
        self.assertAlmostEqual(mmc.parse_duration("795ms"), 0.795)

    def test_unknown_unit_raises(self) -> None:
        """An unrecognised unit is an error, never a zero."""
        for text in ("1.6", "1.6min", "s", "1.6sec"):
            with self.assertRaises(mmc.MeasurementError):
                mmc.parse_duration(text)

    def test_mutant_defaulting_to_zero_is_caught(self) -> None:
        """Mutation: swallow the unknown unit and return 0.0 -- the fail-open case."""
        mutant = load_mutated(
            (
                '    raise MeasurementError(f"unrecognised duration unit in {text!r}")',
                "    return 0.0",
            )
        )
        self.assertEqual(mutant.parse_duration("1.6min"), 0.0)
        with self.assertRaises(mmc.MeasurementError):
            mmc.parse_duration("1.6min")


class ProfileParseTest(unittest.TestCase):
    """The ``-Dprofiler=true`` reader, pinned against captured compiler output."""

    def test_real_output(self) -> None:
        """Import time and the full phase table come back, spaces in names included."""
        import_s, phases = mmc.parse_profile(PROFILER_STDOUT)
        self.assertAlmostEqual(import_s, 1.6)
        self.assertAlmostEqual(phases["interpretation"], 0.795)
        self.assertAlmostEqual(phases["typeclass inference"], 0.00699)
        self.assertAlmostEqual(phases["process pre-definitions"], 0.00197)
        self.assertAlmostEqual(phases["import"], 1.6)
        self.assertEqual(len(phases), 14)

    def test_missing_import_line_raises(self) -> None:
        """Output without an import line cannot yield an import figure."""
        with self.assertRaises(mmc.MeasurementError):
            mmc.parse_profile("cumulative profiling times:\n\telaboration 1ms\n")

    def test_stdout_only_reader_would_see_nothing(self) -> None:
        """The report lives on stderr: reading stdout alone yields no sample at all."""
        with self.assertRaises(mmc.MeasurementError):
            mmc.parse_profile("")

    def test_residual_is_empty_for_a_clean_module(self) -> None:
        """A clean run's whole output is profiler report, so no diagnostic remains."""
        self.assertEqual(mmc.residual_output(PROFILER_STDOUT), [])

    def test_residual_keeps_diagnostics(self) -> None:
        """A compiler message survives the subtraction and is what marks a bad sample."""
        noisy = PROFILER_STDOUT + "X.lean:3:0: error: unknown identifier 'foo'\n"
        residual = mmc.residual_output(noisy)
        self.assertEqual(len(residual), 1)
        self.assertIn("error:", residual[0])


class ChildStreamTest(unittest.TestCase):
    """One invocation against a stub child, which is where the streams are decided."""

    def measure_stub(
        self, module: types.ModuleType, stub: Path, timeout_s: float = 60.0
    ) -> dict[str, object]:
        """Time ``stub`` as if it were ``lean`` on a real library module."""
        target = mmc.REPO_ROOT / TWO_MODULES[0]
        return module.measure_once(str(stub), target, dict(os.environ), timeout_s)

    def test_report_on_stderr_only_is_recovered(self) -> None:
        """The whole profiler report arrives on stderr; the sample must be complete."""
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(Path(tmp), stream="stderr", sleep_s=STUB_SLEEP_S)
            result = self.measure_stub(mmc, stub)
        self.assertTrue(result["valid"], result["problems"])
        self.assertAlmostEqual(float(result["import"]), STUB_IMPORT_S)
        self.assertGreaterEqual(float(result["real"]), STUB_SLEEP_S)
        self.assertAlmostEqual(
            float(result["own"]), float(result["real"]) - STUB_IMPORT_S, places=3
        )
        self.assertEqual(result["phases"]["import"], STUB_IMPORT_S)

    def test_mutant_reading_stdout_only_loses_the_import(self) -> None:
        """Mutation: parse stdout alone -- the bug that made 24 samples 0 valid."""
        mutant = load_mutated(('combined = stdout + "\\n" + stderr', "combined = stdout"))
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(Path(tmp), stream="stderr", sleep_s=STUB_SLEEP_S)
            result = self.measure_stub(mutant, stub)
        self.assertIsNone(result["import"])
        self.assertIsNone(result["own"])
        self.assertFalse(result["valid"])
        self.assertTrue(
            any("import took" in problem for problem in result["problems"]), result["problems"]
        )

    def test_argv_recorded_is_the_argv_spawned(self) -> None:
        """The protocol's argv record is built from the same place the child is."""
        with tempfile.TemporaryDirectory() as tmp:
            seen = Path(tmp) / "argv.json"
            stub = write_stub_lean(
                Path(tmp),
                report="import took 5ms\ncumulative profiling times:\n\timport 5ms\n",
                argv_out=seen,
            )
            result = self.measure_stub(mmc, stub)
            observed = json.loads(seen.read_text(encoding="utf-8"))
        self.assertTrue(result["valid"], result["problems"])
        recorded = mmc.lean_argv(str(stub), mmc.MODULE_PLACEHOLDER)
        target = str(mmc.REPO_ROOT / TWO_MODULES[0])
        self.assertEqual(observed, recorded[:-1] + [target])

    def test_impossible_import_is_rejected(self) -> None:
        """A child claiming more import than the process lasted is not a measurement."""
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(
                Path(tmp),
                report="import took 9999s\ncumulative profiling times:\n\timport 9999s\n",
            )
            result = self.measure_stub(mmc, stub)
        self.assertFalse(result["valid"])
        self.assertEqual(result["import"], 9999.0)
        self.assertTrue(
            any("exceeds" in problem for problem in result["problems"]), result["problems"]
        )

    def test_nonzero_exit_and_error_output_invalidate(self) -> None:
        """A child that failed to elaborate stops early; its wall clock is not a cost."""
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(
                Path(tmp),
                report=STUB_REPORT + "X.lean:1:0: error: unknown identifier 'foo'\n",
                exit_code=1,
            )
            result = self.measure_stub(mmc, stub)
        self.assertFalse(result["valid"])
        self.assertIn("lean exited 1", result["problems"])

    def test_unspawnable_binary_is_an_environment_error(self) -> None:
        """No such ``lean`` raises for the exit-2 path instead of escaping uncaught."""
        with self.assertRaises(mmc.MeasurementError):
            self.measure_stub(mmc, Path("/nonexistent/lean"))


class PlausibilityTest(unittest.TestCase):
    """The bound an import figure has to satisfy to be a timing at all."""

    def test_accepts_a_real_sample(self) -> None:
        """The committed run's own medians pass unchanged."""
        self.assertIsNone(mmc.import_plausibility_problem(1.635, 2.2126))

    def test_rejects_impossible_and_non_finite(self) -> None:
        """Above the wall clock, negative, or not a number: all refused."""
        self.assertIsNotNone(mmc.import_plausibility_problem(9999.0, 2.2))
        self.assertIsNotNone(mmc.import_plausibility_problem(-0.5, 2.2))
        self.assertIsNotNone(mmc.import_plausibility_problem(float("inf"), 2.2))
        self.assertIsNotNone(mmc.import_plausibility_problem(float("nan"), 2.2))

    def test_tolerates_profiler_rounding(self) -> None:
        """Lean prints two or three significant digits, so equality must survive."""
        self.assertIsNone(mmc.import_plausibility_problem(1.6, 1.58))


class SummaryTest(unittest.TestCase):
    """Median / min / max / spread, and which samples are allowed to contribute."""

    def test_summarise(self) -> None:
        """Median (not mean) plus the spread, so a blip is visible but not averaged in."""
        stat = mmc.summarise([2.2, 2.3, 11.3])
        self.assertEqual(stat["median"], 2.3)
        self.assertEqual(stat["min"], 2.2)
        self.assertEqual(stat["max"], 11.3)
        self.assertAlmostEqual(float(stat["spread"]), 9.1)
        self.assertEqual(stat["n"], 3)

    def test_empty(self) -> None:
        """No samples yields nulls and ``n = 0``, never a fabricated zero."""
        self.assertEqual(mmc.summarise([]), {"median": None, "min": None, "max": None,
                                             "spread": None, "n": 0})

    def test_invalid_samples_excluded(self) -> None:
        """A failed invocation contributes no timing (its ``real`` is not a cost)."""
        samples = [
            sample("A", "measure", 2.2, 1.7),
            sample("A", "measure", 2.4, 1.8),
            sample("A", "measure", 0.3, None, valid=False),
        ]
        summary = mmc.summarise_samples(samples)
        self.assertEqual(summary["real"]["n"], 2)
        self.assertEqual(summary["real"]["median"], 2.3)
        self.assertEqual(summary["import"]["n"], 2)


class WarmupTest(unittest.TestCase):
    """Warm-up samples: excluded from the statistics, retained in the record.

    Every assertion here reads the artifact the harness itself wrote. An earlier
    version of this class re-implemented the ``phase == "measure"`` filter and
    then checked its own filtering, which passed no matter what the harness put
    in the summary -- the exact self-fulfilling shape these tests exist to
    prevent.
    """

    STUB_WARM_REAL = 10.0
    STUB_STEADY_REAL = 2.0

    def stub_measure(self, monkeypatched: types.ModuleType, fail_warmup: bool = False):
        """Install a fake ``measure_once``: 10 s on the first pass, 2 s afterwards."""
        calls: list[str] = []

        def fake(lean_bin, module, env, timeout_s):  # noqa: ANN001, ARG001
            calls.append(str(module))
            first_pass = len(calls) <= len(TWO_MODULES)
            real = self.STUB_WARM_REAL if first_pass else self.STUB_STEADY_REAL
            problems = ["stub warm-up failure"] if (first_pass and fail_warmup) else []
            return {
                "module": monkeypatched.rel(Path(module)),
                "real": real,
                "user": 1.2,
                "sys": 1.0,
                "import": real - 0.5,
                "own": 0.5,
                "phases": {},
                "returncode": 0,
                "timed_out": False,
                "problems": problems,
                "valid": not problems,
            }

        monkeypatched.measure_once = fake
        return calls

    def run_harness(
        self, module: types.ModuleType, *, fail_warmup: bool = False
    ) -> tuple[int, dict[str, object]]:
        """Run the whole CLI with the child stubbed; return exit code and artifact."""
        self.stub_measure(module, fail_warmup=fail_warmup)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "artifact.json"
            code, _, _ = run_cli(
                module,
                [
                    "--out", str(out),
                    "--lean-bin", "/nonexistent/lean",
                    "--lean-path", "/nonexistent/lean-path",
                    "--label", "stub",
                    *[str(mmc.REPO_ROOT / name) for name in TWO_MODULES],
                ],
            )
            payload = json.loads(out.read_text(encoding="utf-8"))
        return code, payload

    def test_warmup_excluded_from_the_summary_but_kept_in_the_record(self) -> None:
        """The 10 s warm-up pass must not reach the summary, and must still be stored."""
        code, payload = self.run_harness(fresh_module())
        self.assertEqual(code, 0)
        self.assertEqual(
            payload["sample_counts"],
            {"total": 8, "warmup": 2, "warmup_valid": 2, "measured": 6, "measured_valid": 6},
        )
        self.assertEqual(
            payload["summary"]["real"],
            {"median": 2.0, "min": 2.0, "max": 2.0, "spread": 0.0, "n": 6},
        )
        self.assertEqual(
            [record["real"] for record in payload["samples"] if record["phase"] == "warmup"],
            [self.STUB_WARM_REAL, self.STUB_WARM_REAL],
        )
        self.assertIs(payload["protocol"]["warmup_samples_excluded_from_statistics"], True)

    def test_mutant_counting_warmup_in_the_statistics_is_caught(self) -> None:
        """Mutation: summarise every sample -- the historical 7.0 s inflation returning."""
        mutant = load_mutated(
            (
                'measured = [sample for sample in samples if sample["phase"] == "measure"]',
                "measured = samples",
            )
        )
        _, payload = self.run_harness(mutant)
        self.assertEqual(payload["summary"]["real"]["n"], 8)
        self.assertEqual(payload["summary"]["real"]["max"], self.STUB_WARM_REAL)
        self.assertEqual(payload["sample_counts"]["warmup"], 0)

    def test_mutant_labelling_warmup_as_measured_is_caught(self) -> None:
        """Mutation: label the warm-up pass ``measure`` -- the cold samples come back in."""
        mutant = load_mutated(('passes = [("warmup", index)', 'passes = [("measure", index)'))
        _, payload = self.run_harness(mutant)
        self.assertEqual(payload["summary"]["real"]["n"], 8)
        self.assertEqual(payload["summary"]["real"]["max"], self.STUB_WARM_REAL)

    def test_failed_warmup_fails_the_run(self) -> None:
        """A warm-up that did not complete did not warm anything: exit 1, not 0."""
        code, payload = self.run_harness(fresh_module(), fail_warmup=True)
        self.assertEqual(code, 1)
        self.assertEqual(payload["sample_counts"]["warmup_valid"], 0)
        self.assertEqual(payload["sample_counts"]["measured_valid"], 6)

    def test_pass_major_order(self) -> None:
        """Every module is visited once per pass, so drift spreads instead of pooling."""
        module = fresh_module()
        self.stub_measure(module)
        with contextlib.redirect_stdout(io.StringIO()):
            samples = module.measure(
                [Path("A.lean"), Path("B.lean")], "lean", {}, warmup=0, replicates=3, timeout_s=1.0
            )
        self.assertEqual([s["position_in_pass"] for s in samples], [0, 1, 0, 1, 0, 1])
        self.assertEqual([s["pass"] for s in samples], [0, 0, 1, 1, 2, 2])


class TargetSetTest(unittest.TestCase):
    """The measured set is exactly the requested set, or the run stops."""

    FAMILY = "IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularity*.lean"

    def test_glob_and_dedup(self) -> None:
        """A glob resolves against the repository root; duplicates collapse; order is sorted."""
        modules = mmc.expand_modules([self.FAMILY, self.FAMILY], None)
        self.assertEqual(modules, sorted(set(modules)))
        self.assertTrue(all(path.suffix == ".lean" for path in modules))
        self.assertGreaterEqual(len(modules), 2)

    def test_empty_glob_raises(self) -> None:
        """A pattern matching nothing must not silently measure the empty set."""
        with self.assertRaises(mmc.MeasurementError):
            mmc.expand_modules(["IsingModel/NoSuchDirectory/*.lean"], None)

    def test_missing_path_raises(self) -> None:
        """A named file that does not exist is an error, not a skipped module."""
        with self.assertRaises(mmc.MeasurementError):
            mmc.expand_modules(["IsingModel/NoSuchModule.lean"], None)

    def test_non_lean_raises(self) -> None:
        """Only Lean sources can be timed as modules."""
        with self.assertRaises(mmc.MeasurementError):
            mmc.expand_modules(["lean-toolchain"], None)

    def test_from_file(self) -> None:
        """A list file supplies targets, ignoring blanks and ``#`` comments."""
        with tempfile.TemporaryDirectory() as tmp:
            listing = Path(tmp) / "modules.txt"
            listing.write_text(
                f"# a comment\n\n{TWO_MODULES[1]}\n",
                encoding="utf-8",
            )
            modules = mmc.expand_modules([], str(listing))
        self.assertEqual([mmc.rel(path) for path in modules], [TWO_MODULES[1]])


class CliGuardTest(unittest.TestCase):
    """Usage guards that protect the protocol and the artifact.

    Each case asserts *why* the run stopped. An exit code alone is not evidence:
    ``2`` is also what a missing toolchain returns, so a test that checks only
    the number passes on a machine where the guard was never reached.
    """

    def test_replicate_floor(self) -> None:
        """Fewer than three replicates is refused, naming the floor."""
        code, _, err = run_cli(mmc, ["--replicates", "2", *TWO_MODULES])
        self.assertEqual(code, 2)
        self.assertIn("below the protocol floor", err)

    def test_warmup_floor(self) -> None:
        """``--warmup 0`` is refused rather than recorded as a warm run."""
        code, _, err = run_cli(mmc, ["--warmup", "0", *TWO_MODULES])
        self.assertEqual(code, 2)
        self.assertIn("without a warm-up pass", err)

    def test_refuses_to_overwrite(self) -> None:
        """An existing artifact is never replaced without ``--force``.

        The guard runs before ``elan``/``lake`` are consulted and before any
        module is timed, so this is also what keeps the check from passing for
        the unrelated reason that no toolchain is installed.
        """
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "existing.json"
            out.write_text("{}\n", encoding="utf-8")
            code, _, err = run_cli(mmc, ["--out", str(out), TargetSetTest.FAMILY])
            self.assertEqual(code, 2)
            self.assertIn("artifact already exists", err)
            self.assertEqual(out.read_text(encoding="utf-8"), "{}\n")

    def test_unspawnable_lean_exits_two(self) -> None:
        """A ``lean`` that cannot be executed is an environment exit, not a crash."""
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "artifact.json"
            code, _, err = run_cli(
                mmc,
                [
                    "--out", str(out),
                    "--lean-bin", "/nonexistent/lean",
                    "--lean-path", "/nonexistent/lean-path",
                    str(mmc.REPO_ROOT / TWO_MODULES[0]),
                ],
            )
            self.assertEqual(code, 2)
            self.assertIn("cannot execute lean binary", err)
            self.assertFalse(out.exists())


class FingerprintTest(unittest.TestCase):
    """What the artifact says about the machine and about the package."""

    def test_machine_is_the_hardware_not_the_interpreter(self) -> None:
        """``machine`` comes from a native child, so a translated Python cannot lie.

        On a host where Python runs natively the two fields agree and this pins
        only the layout; on a translated one (Python reporting ``x86_64`` beside
        an arm64 ``lean``) it pins the distinction that matters.
        """
        fingerprint = mmc.hardware_fingerprint()
        self.assertEqual(fingerprint["interpreter_machine"], platform.machine())
        self.assertIsNotNone(fingerprint["machine"])
        self.assertEqual(
            fingerprint["interpreter_translated"],
            fingerprint["machine"] != fingerprint["interpreter_machine"],
        )

    def test_lean_options_come_from_the_lakefile(self) -> None:
        """The omitted-option record is read from the package, not typed out here."""
        options = mmc.lean_options_declared()
        self.assertIn("warningAsError=true", options)
        self.assertTrue(all("=" in option for option in options), options)
        declared = mmc.LAKEFILE.read_text(encoding="utf-8")
        for option in options:
            self.assertIn(option.split("=")[0], declared)

    def test_repository_constants_are_shared_with_audit_gate(self) -> None:
        """One definition of the repository root, not a second copy that can drift."""
        self.assertIs(mmc.REPO_ROOT, audit_gate.REPO_ROOT)
        self.assertIs(mmc.LIB_DIR, audit_gate.LIB_DIR)


class ArtifactShapeTest(unittest.TestCase):
    """The committed artifacts keep every sample, and every sample is valid."""

    def committed_artifacts(self) -> list[Path]:
        """Return the ``measure-module-cost-*.json`` files this repository commits.

        Scoped to what ``git`` tracks, not to what the reports directory
        happens to contain: that directory is also where local scratch runs
        land, including failed ones, and the claim under test is about the
        record the repository publishes.
        """
        pattern = f"{mmc.rel(mmc.DEFAULT_OUT_DIR)}/measure-module-cost-*.json"
        proc = subprocess.run(
            ["git", "-C", str(mmc.REPO_ROOT), "ls-files", "-z", "--", pattern],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return [mmc.REPO_ROOT / name for name in proc.stdout.split("\0") if name]

    def test_committed_artifacts_are_complete_and_valid(self) -> None:
        """Every committed artifact is a whole record of a run with no failed sample."""
        artifacts = self.committed_artifacts()
        # Without this the whole case passes when the glob finds nothing, which
        # is how a check survives the deletion of the thing it checks.
        self.assertTrue(artifacts, "no committed measurement artifact found")
        for path in artifacts:
            payload = json.loads(path.read_text(encoding="utf-8"))
            self.assertIn(payload["schema"], mmc.KNOWN_SCHEMAS, path.name)
            self.assertTrue(payload["samples"], path.name)
            counts = payload["sample_counts"]
            self.assertEqual(counts["total"], len(payload["samples"]), path.name)
            self.assertGreater(counts["measured"], 0, path.name)
            self.assertGreaterEqual(
                counts["measured"] // max(len(payload["modules"]), 1),
                mmc.MIN_REPLICATES,
                path.name,
            )
            self.assertGreaterEqual(counts["warmup"], len(payload["modules"]), path.name)
            self.assertEqual(counts["measured_valid"], counts["measured"], path.name)
            if payload["schema"] == mmc.SCHEMA:
                self.assertEqual(counts["warmup_valid"], counts["warmup"], path.name)
            self.assertIs(
                payload["protocol"]["warmup_samples_excluded_from_statistics"], True, path.name
            )
            self.assertIsNotNone(payload["environment"]["git"]["head"], path.name)
            self.assertIsNotNone(payload["environment"]["lean_toolchain"], path.name)


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())
