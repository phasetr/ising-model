#!/usr/bin/env python3
"""Tests for ``scripts/measure_module_cost.py``.

Run directly (``python3 scripts/test_measure_module_cost.py``) or through the
harness's own ``--self-test`` flag. No ``lean`` and no ``lake`` are needed: the
child process is stubbed, so the suite runs in well under a second and can be
executed while a build holds the machine.

What is worth testing in a stopwatch
------------------------------------
Not the clock. The value of this harness is that the *protocol* it encodes
cannot quietly drift, so the tests pin the four properties whose loss would make
two runs incomparable while every printed number still looks plausible:

1. **A duration it cannot parse must fail, not become zero.** A silently zeroed
   ``import`` reads as a spectacular improvement and is indistinguishable, in
   the artifact, from a real one.
2. **Warm-up samples must stay out of the statistics and inside the record.**
   Counting them re-introduces the cold-page-cache inflation that produced the
   historical 7.0 s figure; dropping them from the JSON removes the evidence
   that the warm-up happened at all.
3. **The target set must be exactly what was asked for.** A glob that matches
   nothing, or a path that is missing, must stop the run rather than shrink a
   "family" to whatever happened to exist.
4. **An artifact must not be silently replaced.** The whole point of the file is
   that it survives.

Each of 1 and 2 is tested in both directions, the idiom of
``scripts/test_audit_gate.py``: a fixture with a known verdict, and a
:func:`load_mutated` re-import with one surgical weakening applied, which is
required to *lose* the property. A mutation whose target stops matching raises,
so it cannot become vacuous after the code moves.
"""

from __future__ import annotations

import json
import sys
import tempfile
import types
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

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
    """Warm-up samples: excluded from the statistics, retained in the record."""

    def stub_measure(self, monkeypatched: types.ModuleType):
        """Install a fake ``measure_once`` returning 10 s warm, 2 s steady."""
        calls: list[str] = []

        def fake(lean_bin, module, env, timeout_s):  # noqa: ANN001, ARG001
            calls.append(str(module))
            first_pass = len(calls) <= 2
            real = 10.0 if first_pass else 2.0
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
                "problems": [],
                "valid": True,
            }

        monkeypatched.measure_once = fake
        return calls

    def test_warmup_excluded_but_recorded(self) -> None:
        """The 10 s warm-up pass must not move the median, and must still be stored."""
        module = fresh_module()
        self.stub_measure(module)
        modules = [Path("A.lean"), Path("B.lean")]
        samples = module.measure(modules, "lean", {}, warmup=1, replicates=3, timeout_s=1.0)
        self.assertEqual(len(samples), 8)
        self.assertEqual(len([s for s in samples if s["phase"] == "warmup"]), 2)
        measured = [s for s in samples if s["phase"] == "measure"]
        self.assertEqual(mmc.summarise_samples(measured)["real"]["median"], 2.0)
        self.assertEqual(mmc.summarise_samples(samples)["real"]["max"], 10.0)

    def test_mutant_labelling_warmup_as_measured_is_caught(self) -> None:
        """Mutation: label the warm-up pass ``measure`` -- the cold samples come back in."""
        mutant = load_mutated(('passes = [("warmup", index)', 'passes = [("measure", index)'))
        self.stub_measure(mutant)
        samples = mutant.measure(
            [Path("A.lean"), Path("B.lean")], "lean", {}, warmup=1, replicates=3, timeout_s=1.0
        )
        measured = [s for s in samples if s["phase"] == "measure"]
        self.assertEqual(len(measured), 8)
        self.assertEqual(mmc.summarise_samples(measured)["real"]["max"], 10.0)

    def test_pass_major_order(self) -> None:
        """Every module is visited once per pass, so drift spreads instead of pooling."""
        module = fresh_module()
        self.stub_measure(module)
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
                "# a comment\n\nIsingModel/AmbientLattice/SpecialCases/"
                "PartitionFreeEnergyRegularityH.lean\n",
                encoding="utf-8",
            )
            modules = mmc.expand_modules([], str(listing))
        self.assertEqual([mmc.rel(path) for path in modules],
                         ["IsingModel/AmbientLattice/SpecialCases/"
                          "PartitionFreeEnergyRegularityH.lean"])


class CliGuardTest(unittest.TestCase):
    """Usage guards that protect the protocol and the artifact."""

    def test_replicate_floor(self) -> None:
        """Fewer than three replicates is refused (exit 2), before anything is run."""
        code = mmc.main(["--replicates", "2", "IsingModel.lean"])
        self.assertEqual(code, 2)

    def test_refuses_to_overwrite(self) -> None:
        """An existing artifact is never replaced without ``--force``."""
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "existing.json"
            out.write_text("{}\n", encoding="utf-8")
            code = mmc.main(["--out", str(out), TargetSetTest.FAMILY])
            self.assertEqual(code, 2)
            self.assertEqual(out.read_text(encoding="utf-8"), "{}\n")


class ArtifactShapeTest(unittest.TestCase):
    """The committed artifact keeps every sample, not only the aggregate."""

    def test_committed_artifacts_parse_and_carry_samples(self) -> None:
        """Every ``measure-module-cost-*.json`` in the repository is a complete record."""
        artifacts = sorted(mmc.DEFAULT_OUT_DIR.glob("measure-module-cost-*.json"))
        for path in artifacts:
            payload = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(payload["schema"], mmc.SCHEMA, path.name)
            self.assertTrue(payload["samples"], path.name)
            counts = payload["sample_counts"]
            self.assertEqual(counts["total"], len(payload["samples"]), path.name)
            self.assertGreaterEqual(
                counts["measured"] // max(len(payload["modules"]), 1),
                mmc.MIN_REPLICATES,
                path.name,
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
