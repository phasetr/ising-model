#!/usr/bin/env python3
"""Tests for ``scripts/measure_module_cost.py``.

Run directly (``python3 scripts/test_measure_module_cost.py``) or through the
harness's own ``--self-test`` flag.

No ``lean``, no ``lake`` and no ``elan``: the timed child is either stubbed out
in Python or replaced by a small stub executable that prints a canned profiler
report, so nothing here compiles anything and the suite is safe to run while a
build holds the machine. It is not instantaneous -- the stub-executable cases
sleep a few tenths of a second on purpose, so that a reported ``import`` is
below the wall clock the harness measures around them. Expect a few seconds.

Scope: the harness, never a committed artifact
----------------------------------------------
Every case here is about what ``measure_module_cost.py`` *does*. None reads a
committed measurement artifact and judges it. That second layer existed and was
deleted: three rounds of review found seven fail-open holes in it, three of them
introduced by the round that was meant to close the previous three, and the
rule declared before that round -- another round of fail-open holes in the
artifact-validation layer and the layer goes rather than being hardened again --
fired. The evidence it used to guard is committed and unchanged; what is gone is
the machinery that re-judged it on every CI run without converging.

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
3. **An impossible timing must be rejected**, and the profiler's two statements
   of the import figure must agree. ``import`` is a subinterval of the process
   ``real`` was measured around, so a child claiming more is not a slow module;
   and a report whose ``import took`` line contradicts its own ``import`` table
   row is not the report this parser was written against.
4. **Warm-up samples must stay out of the statistics and inside the record**,
   and a failed warm-up must fail the run. Counting warm-up samples
   re-introduces the cold-page-cache inflation that produced the historical
   7.0 s figure; dropping them from the JSON removes the evidence that the
   warm-up happened at all.
5. **The target set must be exactly what was asked for**, each file once. A
   glob that matches nothing, or a path that is missing, must stop the run
   rather than shrink a "family" to whatever happened to exist; and a glob that
   reaches one file by several spellings must not measure it several times.
6. **An artifact must not be silently replaced.** ``--out`` onto an existing
   file needs ``--force``, and the refusal has to come before any module is
   timed.
7. **A guard that cannot be evaluated must stop the run.** The protocol
   discards samples taken beside a foreign ``lean``; a harness that records the
   count as ``null`` when it cannot take it leaves that rule inert while the
   artifact still looks compliant.
8. **The measured bytes must be identifiable afterwards.** ``git`` HEAD does
   not identify them on a dirty tree, so the porcelain digest, the dirty paths
   and a hash per measured module have to be in the record.
9. **The registered machine-load guard's inputs must be recorded per sample**,
   with a probe that cannot answer saying so rather than leaving a ``null``.
   The harness records them and judges none of them: section 4.3 of the design
   report owns that rule.

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
import hashlib
import io
import json
import os
import platform
import stat
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


# A stubbed run's two regimes: the discarded warm-up pass is expensive (cold
# page cache), every measured pass afterwards is cheap. The gap is what makes
# "did a warm-up sample reach the statistics" visible in the summary.
STUB_WARM_REAL = 10.0
STUB_STEADY_REAL = 2.0


def install_stub_measure(module: types.ModuleType, *, fail_warmup: bool = False) -> list[str]:
    """Replace ``measure_once`` with a fake child and return the call log.

    10 s on the first pass over the target set, 2 s on every pass after it.
    ``fail_warmup`` makes the first pass report a problem, which is how a
    warm-up that never warmed anything is simulated.
    """
    calls: list[str] = []

    def fake(lean_bin, module_path, env, timeout_s):  # noqa: ANN001, ARG001
        calls.append(str(module_path))
        first_pass = len(calls) <= len(TWO_MODULES)
        real = STUB_WARM_REAL if first_pass else STUB_STEADY_REAL
        problems = ["stub warm-up failure"] if (first_pass and fail_warmup) else []
        return {
            "module": module.rel(Path(module_path)),
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

    module.measure_once = fake
    return calls


def install_stub_census(module: types.ModuleType, counts: tuple[int | None, ...]) -> None:
    """Pin the process guard to ``counts``, consumed one per census, last value repeating.

    Real ``pgrep``/``ps`` results would make every stubbed run depend on what
    else happens to be resident, and the sandbox this suite also runs in cannot
    answer either probe at all.
    """
    remaining = list(counts)

    def fake() -> dict[str, object]:
        count = remaining.pop(0) if len(remaining) > 1 else remaining[0]
        return {"method": "stub", "count": count, "error": None if count is not None else "stub"}

    module.lean_process_census = fake


def run_stub_cli(
    module: types.ModuleType,
    *,
    fail_warmup: bool = False,
    census_counts: tuple[int | None, ...] = (0,),
    argv_extra: tuple[str, ...] = (),
) -> tuple[int, dict[str, object]]:
    """Run the whole CLI with the timed child and the process census stubbed.

    Returns the exit code and the artifact the harness wrote, because that
    artifact -- not a filter the test re-implements -- is the thing under test.
    """
    install_stub_measure(module, fail_warmup=fail_warmup)
    install_stub_census(module, census_counts)
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "artifact.json"
        code, _, _ = run_cli(
            module,
            [
                "--out", str(out),
                "--lean-bin", "/nonexistent/lean",
                "--lean-path", "/nonexistent/lean-path",
                "--label", "stub",
                *argv_extra,
                *[str(mmc.REPO_ROOT / name) for name in TWO_MODULES],
            ],
        )
        payload = json.loads(out.read_text(encoding="utf-8"))
    return code, payload


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

    def test_table_row_must_agree_with_the_standalone_line(self) -> None:
        """One quantity printed twice: if the two disagree, neither is this run's import."""
        with self.assertRaises(mmc.MeasurementError) as caught:
            mmc.parse_profile("import took 1.6s\ncumulative profiling times:\n\timport 0.9s\n")
        self.assertIn("disagrees with itself", str(caught.exception))

    def test_missing_table_row_is_refused(self) -> None:
        """A report the cross-check cannot be performed on is not a report to record."""
        with self.assertRaises(mmc.MeasurementError) as caught:
            mmc.parse_profile(
                "import took 1.6s\ncumulative profiling times:\n\telaboration 36.8ms\n"
            )
        self.assertIn("cannot be compared", str(caught.exception))

    def test_mutant_skipping_the_cross_check_accepts_a_contradiction(self) -> None:
        """Mutation: drop the comparison -- a self-contradicting report parses again."""
        mutant = load_mutated(
            (
                '    if abs(phases["import"] - import_s) > IMPORT_CONSISTENCY_ABS_TOLERANCE_S:',
                "    if False:",
            )
        )
        import_s, _ = mutant.parse_profile(
            "import took 1.6s\ncumulative profiling times:\n\timport 0.9s\n"
        )
        self.assertAlmostEqual(import_s, 1.6)

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

    def test_warmup_excluded_from_the_summary_but_kept_in_the_record(self) -> None:
        """The 10 s warm-up pass must not reach the summary, and must still be stored."""
        code, payload = run_stub_cli(fresh_module())
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
            [STUB_WARM_REAL, STUB_WARM_REAL],
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
        _, payload = run_stub_cli(mutant)
        self.assertEqual(payload["summary"]["real"]["n"], 8)
        self.assertEqual(payload["summary"]["real"]["max"], STUB_WARM_REAL)
        self.assertEqual(payload["sample_counts"]["warmup"], 0)

    def test_mutant_labelling_warmup_as_measured_is_caught(self) -> None:
        """Mutation: label the warm-up pass ``measure`` -- the cold samples come back in."""
        mutant = load_mutated(('passes = [("warmup", index)', 'passes = [("measure", index)'))
        _, payload = run_stub_cli(mutant)
        self.assertEqual(payload["summary"]["real"]["n"], 8)
        self.assertEqual(payload["summary"]["real"]["max"], STUB_WARM_REAL)

    def test_failed_warmup_fails_the_run(self) -> None:
        """A warm-up that did not complete did not warm anything: exit 1, not 0."""
        code, payload = run_stub_cli(fresh_module(), fail_warmup=True)
        self.assertEqual(code, 1)
        self.assertEqual(payload["sample_counts"]["warmup_valid"], 0)
        self.assertEqual(payload["sample_counts"]["measured_valid"], 6)

    def test_pass_major_order(self) -> None:
        """Every module is visited once per pass, so drift spreads instead of pooling."""
        module = fresh_module()
        install_stub_measure(module)
        with contextlib.redirect_stdout(io.StringIO()):
            samples = module.measure(
                [Path("A.lean"), Path("B.lean")], "lean", {}, warmup=0, replicates=3, timeout_s=1.0
            )
        self.assertEqual([s["position_in_pass"] for s in samples], [0, 1, 0, 1, 0, 1])
        self.assertEqual([s["pass"] for s in samples], [0, 0, 1, 1, 2, 2])


class TargetSetTest(unittest.TestCase):
    """The measured set is exactly the requested set, or the run stops."""

    FAMILY = "IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularity*.lean"
    # The same eight files, reached through a directory the pattern steps into
    # and back out of. Spelled differently, resolved identically -- the shape
    # ``IsingModel/**/../*.lean`` takes to an extreme (7620 paths for 1174
    # files) when the deduplication compares spellings.
    DETOUR = (
        "IsingModel/AmbientLattice/SpecialCases/../SpecialCases/"
        "PartitionFreeEnergyRegularity*.lean"
    )

    def test_glob_and_dedup(self) -> None:
        """A glob resolves against the repository root; duplicates collapse; order is sorted."""
        modules = mmc.expand_modules([self.FAMILY, self.FAMILY], None)
        self.assertEqual(modules, sorted(set(modules)))
        self.assertTrue(all(path.suffix == ".lean" for path in modules))
        self.assertGreaterEqual(len(modules), 2)

    def test_the_same_file_under_two_spellings_is_measured_once(self) -> None:
        """Deduplication is by file identity, so a detour cannot double the sample count."""
        direct = mmc.expand_modules([self.FAMILY], None)
        both = mmc.expand_modules([self.FAMILY, self.DETOUR], None)
        self.assertEqual(both, direct)
        self.assertTrue(all(path == path.resolve() for path in both), both)

    def test_mutant_deduplicating_by_spelling_measures_each_file_twice(self) -> None:
        """Mutation: key by the spelling instead of the file -- one timing per spelling."""
        mutant = load_mutated(
            (
                "found.setdefault((info.st_dev, info.st_ino), resolved)",
                "found.setdefault(path.as_posix(), resolved)",
            )
        )
        both = mutant.expand_modules([self.FAMILY, self.DETOUR], None)
        self.assertEqual(len(both), 2 * len(mmc.expand_modules([self.FAMILY], None)))

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

    def test_non_finite_or_non_positive_timeout_is_a_usage_error(self) -> None:
        """``--timeout nan``/``inf`` used to raise from ``subprocess`` with no artifact."""
        for value in ("nan", "inf", "-inf", "0", "-5"):
            # ``--timeout=-5`` rather than two tokens: argparse reads a leading
            # ``-inf`` as an option name and never reaches the guard.
            code, _, err = run_cli(mmc, [f"--timeout={value}", *TWO_MODULES])
            self.assertEqual(code, 2, value)
            self.assertIn("not a positive finite number of seconds", err)

    def test_a_non_finite_timeout_would_raise_from_subprocess(self) -> None:
        """Why the guard exists: the value is converted to an integer deep inside."""
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(Path(tmp))
            with self.assertRaises(ValueError):
                mmc.measure_once(
                    str(stub),
                    mmc.REPO_ROOT / TWO_MODULES[0],
                    dict(os.environ),
                    float("nan"),
                )

    def test_unspawnable_lean_exits_two(self) -> None:
        """A ``lean`` that cannot be executed is an environment exit, not a crash."""
        module = fresh_module()
        install_stub_census(module, (0,))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "artifact.json"
            code, _, err = run_cli(
                module,
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

    def test_machine_state_records_every_input_and_nulls_none_of_them(self) -> None:
        """The registered guard's three inputs are recorded, a failed probe included.

        ``pmset -g therm`` exits 0 in this sandbox while printing that it could
        not read the thermal state, so the assertion is that the record shows
        the exit code and the output -- not that the state was readable.
        """
        state = mmc.machine_state()
        self.assertEqual(set(state), {"loadavg", "ac_power", "thermal"})
        load = state["loadavg"]
        if isinstance(load, list):
            self.assertEqual(len(load), 3)
        else:
            self.assertIn("unavailable", str(load))
        for key in ("ac_power", "thermal"):
            probe = state[key]
            self.assertEqual(set(probe), {"command", "exit_code", "output"}, key)
            self.assertTrue(str(probe["command"]).startswith("pmset "), key)
            self.assertIsInstance(probe["exit_code"], int, key)
            self.assertIsInstance(probe["output"], list, key)

    def test_every_sample_carries_its_own_machine_state(self) -> None:
        """Per sample, not once per run: the registered guard is per replicate."""
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub_lean(Path(tmp), stream="stderr", sleep_s=STUB_SLEEP_S)
            result = mmc.measure_once(
                str(stub), mmc.REPO_ROOT / TWO_MODULES[0], dict(os.environ), 60.0
            )
        self.assertEqual(set(result["machine_state"]), {"loadavg", "ac_power", "thermal"})


class ProcessGuardTest(unittest.TestCase):
    """The serial-run precondition: counted, recorded as a number, or the run stops.

    The committed 2026-07-31 artifact recorded ``other_lean_processes_at_start:
    null`` because ``pgrep`` cannot answer inside this repository's sandbox.
    Nothing was wrong with that run, but the protocol's "discard any sample
    taken beside a foreign ``lean``" rule had no input and could not have fired,
    which is indistinguishable in the artifact from a rule that fired and passed.
    """

    def test_census_answers_with_a_method_or_with_an_error(self) -> None:
        """Whatever the environment allows, the shape is a count and its provenance."""
        census = mmc.lean_process_census()
        self.assertEqual(set(census), {"method", "count", "error"})
        if census["count"] is None:
            self.assertIsNone(census["method"])
            self.assertTrue(census["error"])
        else:
            self.assertIsInstance(census["count"], int)
            self.assertGreaterEqual(int(census["count"]), 0)
            self.assertIn(census["method"], ("pgrep", "ps"))
            self.assertIsNone(census["error"])

    def test_a_refusing_pgrep_is_not_read_as_zero(self) -> None:
        """``pgrep`` exiting 3 means "cannot get the process list", not "none running"."""
        module = fresh_module()
        module.run_capture = lambda cmd, cwd=None: (3, "", "pgrep: Cannot get process list")
        with self.assertRaises(module.MeasurementError):
            module._census_via_pgrep()

    def test_ps_is_the_fallback_and_counts_lean_and_lake(self) -> None:
        """One probe being unavailable is not evidence that the machine is quiet."""
        module = fresh_module()

        def fake(cmd, cwd=None):  # noqa: ANN001, ARG001
            if cmd[0] == "pgrep":
                return (3, "", "Cannot get process list")
            if cmd[0] == "ps":
                return (0, "/usr/bin/lean\n/bin/zsh\nlake\n/usr/bin/leanls\n", "")
            return (127, "", "unexpected command")

        module.run_capture = fake
        self.assertEqual(
            module.lean_process_census(), {"method": "ps", "count": 2, "error": None}
        )

    def test_an_uncountable_guard_refuses_to_measure(self) -> None:
        """No count, no run: recording ``null`` is what made the discard rule inert."""
        module = fresh_module()
        install_stub_measure(module)
        install_stub_census(module, (None,))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "artifact.json"
            code, _, err = run_cli(
                module,
                [
                    "--out", str(out),
                    "--lean-bin", "/nonexistent/lean",
                    "--lean-path", "/nonexistent/lean-path",
                    *[str(mmc.REPO_ROOT / name) for name in TWO_MODULES],
                ],
            )
            self.assertEqual(code, 2)
            self.assertIn("refusing to record the guard as unknown", err)
            self.assertFalse(out.exists())

    def test_a_clean_guard_is_recorded_as_such(self) -> None:
        """Zero at both ends is the only state that lets the run succeed."""
        code, payload = run_stub_cli(fresh_module(), census_counts=(0,))
        self.assertEqual(code, 0)
        guard = payload["environment"]["process_guard"]
        self.assertEqual(guard["at_start"], 0)
        self.assertEqual(guard["at_end"], 0)
        self.assertIs(guard["clean"], True)
        self.assertEqual(payload["environment"]["other_lean_processes_at_start"], 0)

    def test_a_process_appearing_mid_run_fails_the_run(self) -> None:
        """Clean at the start is not clean: the end count is what catches an intruder."""
        code, payload = run_stub_cli(fresh_module(), census_counts=(0, 1))
        self.assertEqual(code, 1)
        guard = payload["environment"]["process_guard"]
        self.assertEqual((guard["at_start"], guard["at_end"]), (0, 1))
        self.assertIs(guard["clean"], False)
        # The samples are kept: nothing is killed and nothing is deleted, the
        # run simply reports what it was taken beside.
        self.assertEqual(payload["sample_counts"]["measured_valid"], 6)

    def test_mutant_treating_an_unknown_count_as_clean_is_caught(self) -> None:
        """Mutation: accept a ``None`` count -- the exact state the committed run was in."""
        mutant = load_mutated(('if census["count"] is None:', "if False:"))
        install_stub_measure(mutant)
        install_stub_census(mutant, (None,))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "artifact.json"
            code, _, _ = run_cli(
                mutant,
                [
                    "--out", str(out),
                    "--lean-bin", "/nonexistent/lean",
                    "--lean-path", "/nonexistent/lean-path",
                    *[str(mmc.REPO_ROOT / name) for name in TWO_MODULES],
                ],
            )
            payload = json.loads(out.read_text(encoding="utf-8"))
        self.assertEqual(code, 1)
        self.assertIsNone(payload["environment"]["other_lean_processes_at_start"])


class ProvenanceTest(unittest.TestCase):
    """Which bytes were measured: HEAD alone does not say, on a dirty tree."""

    def test_git_record_names_the_dirty_paths_and_digests_them(self) -> None:
        """``dirty: true`` without the paths leaves the measurement unattributable."""
        fingerprint = mmc.git_fingerprint()
        self.assertIsNotNone(fingerprint["head"])
        self.assertIsInstance(fingerprint["dirty_paths"], list)
        self.assertEqual(fingerprint["dirty"], bool(fingerprint["dirty_paths"]))
        self.assertTrue(str(fingerprint["status_digest"]).startswith("sha256:"))
        self.assertEqual(len(str(fingerprint["status_digest"])), len("sha256:") + 64)

    def test_module_digests_pin_the_measured_bytes(self) -> None:
        """The hash is over the module's raw bytes, computed here independently."""
        modules = [mmc.REPO_ROOT / name for name in TWO_MODULES]
        digests = mmc.module_digests(modules)
        self.assertEqual(sorted(digests), sorted(TWO_MODULES))
        for name, recorded in digests.items():
            expected = hashlib.sha256((mmc.REPO_ROOT / name).read_bytes()).hexdigest()
            self.assertEqual(recorded, f"sha256:{expected}", name)

    def test_the_artifact_carries_the_provenance(self) -> None:
        """A run records the digests beside the modules it names, one per target."""
        code, payload = run_stub_cli(fresh_module())
        self.assertEqual(code, 0)
        self.assertEqual(sorted(payload["module_digests"]), sorted(payload["modules"]))
        self.assertIsNotNone(payload["environment"]["git"]["status_digest"])
        self.assertIsInstance(payload["environment"]["git"]["dirty_paths"], list)

    def test_mutant_recording_only_the_dirty_flag_is_caught(self) -> None:
        """Mutation: drop the porcelain digest -- back to a boolean nobody can act on."""
        mutant = load_mutated(
            ('"status_digest": digest(status) if code_status == 0 else None,',
             '"status_digest": None,')
        )
        _, payload = run_stub_cli(mutant)
        self.assertIsNone(payload["environment"]["git"]["status_digest"])
        self.assertIsNotNone(mmc.git_fingerprint()["status_digest"])


def run_suite() -> int:
    """Run every test. Return ``0`` on success, ``1`` otherwise."""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(run_suite())
