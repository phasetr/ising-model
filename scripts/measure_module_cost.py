#!/usr/bin/env python3
"""Per-module Lean build-cost harness for the IsingModel library.

Measures what one module costs to elaborate, under the *canonical protocol* this
repository settled on in ``.self-local/reports/perf-4724-fixed-cost-reconciliation.md``
(2026-07-26, anchor ``4f9b7235``). Uses only the Python 3 standard library.

Why this exists as a script and not as prose
--------------------------------------------
The protocol that produced the figures in dispute survived only as prose, and
its raw samples are gone: the reconciliation report's own "Artifacts" section
records every sample directory as ephemeral and already deleted. The
consequence was observed, not feared. That report (2026-07-26) decomposes the
two per-module figures (~7.0 s and ~1.8 s) into a metric difference plus a
page-cache difference, yet issue #4794 was opened three days later, on
2026-07-29, still describing them as measurements of one quantity that
"disagree by approximately 4.5x" -- because neither figure could be re-derived
without re-inventing the protocol. A protocol that has to be re-invented is a
protocol that will differ, and two runs under different protocols are not
comparable at all.

The narrower claim is the true one: *this* protocol was prose only. One earlier
build-timing protocol here was committed, with its raw samples --
``.self-local/reports/perf-isdefeq-cluster-artifacts/measure.sh`` and the
``*_trace.out`` logs beside it, added by commit ``b4bec721``. That script is
also the reason a committed harness needs an owner: it times ``lake env lean``,
the exact invocation section 7 of the reconciliation retires, and nothing
beside it said so until it was annotated as superseded by this harness. An
executable protocol nobody maintains becomes a superseded twin someone re-runs.

So the protocol is executable, and the samples are an artifact:

* bare ``lean``, **never** ``lake env lean``. The wrapper costs a constant
  ~1.07 s per invocation that a real ``lake build`` never pays (lake spawns
  ``lean`` directly), which is one half of the historical 4.5x gap.
* ``LEAN_PATH`` obtained **once**, from ``lake env printenv LEAN_PATH``, so the
  wrapper is paid once for the whole run instead of once per sample.
* **serial** execution, one ``lean`` process at a time. Import work is
  page-fault/mmap bound: at 10-way concurrency total CPU inflates 1.6-2.5x,
  almost entirely in ``sys``, so per-module numbers taken from a parallel run
  measure contention, not work.
* a **warm-up pass** over the target set whose samples are recorded but
  **excluded from the statistics**. This is the other half of the gap: the OS
  page cache alone swings ``import`` by 5-15x (11.3 s cold vs 1.75 s warm on the
  same file, same tree, same session) while ``user`` CPU stays flat at
  1.8-2.0 s. A "warm cache" claim about ``.lake/build`` says nothing about the
  page cache.
* **>= 3 replicates** per module, reported as median plus min-max spread. Never
  a mean: the historical data contains single-sample "contention blips" (11.31 s
  in a 3-sample set) that move a mean and not a median.
* ``user`` CPU reported next to ``real`` for every sample, because a large
  ``real``/``user`` gap *is* the page-cache-miss signature, and it is the only
  cheap way a reader can tell a warm run from a cold one after the fact.

Effect on the build cache: none. ``lean`` is invoked with no ``-o``/``-i``/``-c``
output flag, so it writes no ``.olean``/``.ilean``/``.c`` and cannot disturb a
warm ``.lake/build``. The harness also never removes build artifacts, and never
deletes its own output.

Metrics recorded per sample
---------------------------
``lean`` writes its **entire** ``-Dprofiler=true`` report to **stderr**, not to
stdout (stdout stays empty for a clean module), so both streams are read and
concatenated before parsing. A harness that reads stdout only silently gets no
import figure at all; here that is a hard sample failure rather than a zero.

``real``    wall clock around the child process (``time.monotonic``).
``user``    child user CPU (``resource.RUSAGE_CHILDREN`` delta; the run is
            serial and single-threaded, so the delta is exactly this child).
``sys``     child system CPU, same source. Where page-cache misses land.
``import``  the import phase, parsed from ``-Dprofiler=true`` output.
``own``     ``real - import``: lean init, parsing, elaboration, interpretation.
Plus the whole ``cumulative profiling times`` table, verbatim as parsed, so a
later question about a phase this docstring does not name can be answered from
the artifact instead of from a new run.

``import`` is a subinterval of the very process ``real`` was measured around,
so a child reporting an ``import`` above that wall clock is not reporting a
slow import, it is reporting something this harness must not average. Such a
sample is rejected, not recorded as a measurement with a negative ``own``.

The profiler states the import figure **twice** -- once as the standalone
``import took ...`` line and once as the ``import`` row of the cumulative table
-- and this harness reads the first while the artifact publishes both. The two
are cross-checked against each other and a disagreement fails the sample: two
figures for one quantity that are never compared are one unchecked figure and
one decoration.

Conditions the run refuses to proceed without
---------------------------------------------
The protocol's discard rules can only operate on facts that were recorded, so
each of them is recorded as a *value*, never as "unknown":

* **no foreign ``lean``/``lake`` process.** Counted before the first sample and
  after the last (``pgrep``, falling back to ``ps``). A count that cannot be
  taken at all is a refusal to start, not a ``null`` in the artifact: a null
  there silently disables the rule that a contaminated sample is discarded. A
  count above zero fails the run, with every sample still written.
* **which bytes were measured.** ``git`` HEAD alone does not identify them on a
  dirty tree, so the artifact also carries the ``git status --porcelain``
  digest, the dirty paths themselves, and a SHA-256 of every measured module's
  content. A later reader can then tell whether a re-run measured the same
  source, instead of inferring it from a branch name.

What this harness does not reproduce
------------------------------------
``lake build`` passes the package's ``[leanOptions]`` (``lakefile.toml``) to
every ``lean`` it spawns; this harness passes only ``-Dprofiler=true``. The
exact argv and the list of omitted options are recorded in
``protocol.invocation``, so the gap is checkable in the artifact instead of
resting on this paragraph. An A/B run during the review of this harness put the
difference inside run-to-run noise on the measured family (``own`` median
0.552 s bare against 0.587 s with the options, versus a 0.177 s ``own`` spread
within the run itself), so the recorded medians stand as measured; the omission
is a known bias to re-check, not a correction to apply.

Usage
-----
    python3 scripts/measure_module_cost.py [options] MODULE [MODULE ...]

``MODULE`` is a path to a ``.lean`` file, or a glob (quoted, so the shell does
not expand it) resolved against the repository root; ``--from-file`` reads a
newline-separated list. Examples::

    # one family, canonical settings (1 warm-up pass, 3 replicates)
    python3 scripts/measure_module_cost.py --label pfer \\
        'IsingModel/AmbientLattice/SpecialCases/PartitionFreeEnergyRegularity*.lean'

    # more replicates, explicit output path
    python3 scripts/measure_module_cost.py --replicates 5 \\
        --out .self-local/reports/measure-foo.json --from-file modules.txt

Output: a JSON document holding **every individual sample** (warm-up samples
included, flagged and excluded from the statistics), per-module and overall
summaries (median / min / max / spread / n), the provenance of the measured
bytes (git HEAD, branch, porcelain digest and dirty paths, plus a SHA-256 per
measured module), and an environment fingerprint (``lean-toolchain``, lean
binary and version, target and repository module counts, load average,
hardware, timestamp, and the process-guard counts). Written to
``--out``, or to
``.self-local/reports/measure-module-cost-<label>-<timestamp>.json``. An
existing file is never overwritten without ``--force``.

Exit code 0 iff **every** sample was valid (lean exited 0, the profiler output
parsed, and the import figure was possible) *and* the process guard held,
warm-up passes included: a run whose warm-up did not complete never warmed the
page cache, so its measured samples were not taken under this protocol at all.
1 if any sample failed or a foreign ``lean``/``lake`` process was seen; 2 on a
usage/environment error, including a ``lean`` that cannot be executed and an
environment where the process guard cannot be evaluated.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import re
import resource
import statistics
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from audit_gate import (  # noqa: E402  (path bootstrap must precede the import)
    LIB_DIR,
    REPO_ROOT,
    rel as _repo_rel,
)

TOOLCHAIN_FILE = REPO_ROOT / "lean-toolchain"
LAKEFILE = REPO_ROOT / "lakefile.toml"
DEFAULT_OUT_DIR = REPO_ROOT / ".self-local" / "reports"

# Version tag of the JSON schema, so a consumer can tell two artifacts apart
# after a field is added or renamed. 2 made ``protocol.invocation`` the exact
# argv record and ``environment.platform.machine`` the hardware rather than the
# interpreter's own (possibly translated) architecture; 3 made the process
# guard a recorded value instead of a nullable one and added the provenance of
# the measured bytes (porcelain digest, dirty paths, per-module hashes).
SCHEMA = "ising-model/measure_module_cost/3"

# Schema tags whose artifacts remain readable by this file's consumers. Listed
# rather than open-ended: an artifact written by a *newer* schema must fail a
# reader that predates it instead of being parsed on the assumption that fields
# only ever get added.
KNOWN_SCHEMAS = (
    SCHEMA,
    "ising-model/measure_module_cost/2",
    "ising-model/measure_module_cost/1",
)

# The canonical protocol's replicate floor. Enforced rather than defaulted: the
# floor is the part of the protocol that a hurried run drops first, and a
# 1-sample "median" is indistinguishable in the artifact from a 3-sample one
# unless the tool refuses to produce it.
MIN_REPLICATES = 3

# The warm-up floor, enforced for the same reason. Without a warm-up pass the
# statistics describe the OS page cache rather than the modules (5-15x on
# ``import``), and the artifact would still carry the protocol's
# "warm-up samples excluded" wording while no warm-up had run.
MIN_WARMUP = 1

# Tolerance when checking a profiler figure against the wall clock measured
# around the same process. Lean prints durations to two or three significant
# digits, so a genuine import can round *up* past ``real`` by a hair; anything
# beyond this is a child that is not reporting on the run just timed.
IMPORT_REL_TOLERANCE = 0.01
IMPORT_ABS_TOLERANCE_S = 0.05

# Tolerance when checking the standalone ``import took`` line against the
# ``import`` row of the same report. These are one quantity printed twice by one
# process, so they agree exactly in every sample recorded so far; the slack is
# only against a future formatting change, not against a real disagreement.
IMPORT_CONSISTENCY_ABS_TOLERANCE_S = 1e-6

# Timeout for a single ``lean`` invocation. Generous: a cold page cache has been
# observed to turn a 2 s module into a 28 s one without anything being wrong.
DEFAULT_TIMEOUT_S = 900.0

# Process names whose presence voids the serial-run precondition. ``lake`` as
# well as ``lean``: a concurrent ``lake build`` competes for the same cores and
# the same page cache even before it has spawned its first ``lean``.
GUARDED_PROCESS_NAMES = ("lean", "lake")

# Glob metacharacters that make an argument a pattern rather than a literal path.
_GLOB_CHARS = "*?["

# The only flag the timed child is given. A constant because the argv recorded
# in the artifact and the argv actually spawned are both built from it by
# :func:`lean_argv`; a protocol field maintained by hand drifts from the run it
# claims to describe, and nothing in the artifact would show it.
LEAN_FLAGS = ("-Dprofiler=true",)

# Placeholder standing for the absolute module path in the recorded argv.
MODULE_PLACEHOLDER = "MODULE"

# ``[leanOptions]`` key/value lines of ``lakefile.toml``, comments stripped.
_LEAN_OPTION_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*=\s*([^#\s]+)")

# ``-Dprofiler=true`` prints ``import took <duration>`` before the cumulative
# table, and repeats the same figure inside the table as the ``import`` row.
_IMPORT_LINE_RE = re.compile(r"^import took (?P<dur>.+?)\s*$", re.MULTILINE)
_PROFILE_ROW_RE = re.compile(
    r"^[ \t]+(?P<name>\S.*?)[ \t]+(?P<dur>[0-9.]+(?:e[-+]?[0-9]+)?\s*(?:ns|us|µs|ms|s))$"
)

# Duration suffixes Lean's profiler emits, longest suffix first so that ``ms``
# is never read as ``s``. An unknown suffix must *fail*, not default to zero: a
# silently zeroed import time would look like a spectacular improvement.
_DURATION_UNITS = (
    ("ns", 1e-9),
    ("us", 1e-6),
    ("µs", 1e-6),
    ("ms", 1e-3),
    ("s", 1.0),
)


class MeasurementError(Exception):
    """A usage or environment problem that makes measurement impossible."""


def parse_duration(text: str) -> float:
    """Return ``text`` (e.g. ``"1.68s"``, ``"36.8ms"``) as seconds.

    Raises :class:`MeasurementError` on an unrecognised unit or mantissa. The
    strictness is deliberate: the alternative to raising is returning ``0.0``
    for a duration the parser did not understand, which enters the artifact as
    a real measurement and cannot be told apart from one afterwards.
    """
    token = text.strip()
    for suffix, scale in sorted(_DURATION_UNITS, key=lambda item: -len(item[0])):
        if token.endswith(suffix):
            mantissa = token[: -len(suffix)].strip()
            try:
                return float(mantissa) * scale
            except ValueError as exc:
                raise MeasurementError(f"unparsable duration mantissa {text!r}") from exc
    raise MeasurementError(f"unrecognised duration unit in {text!r}")


def parse_profile(output: str) -> tuple[float, dict[str, float]]:
    """Return ``(import seconds, phase table)`` from ``-Dprofiler=true`` output.

    ``output`` must be the child's stdout **and** stderr: Lean emits the whole
    profiler report on stderr. The import figure is taken from the standalone
    ``import took ...`` line, which the import phase emits directly. The
    cumulative table is returned whole (phase name -> seconds) so the artifact
    keeps every phase the run saw, not only the ones summarised here.

    The report states the import figure twice, and the two statements are
    checked against each other here. A missing ``import`` row, or a row that
    disagrees with the standalone line, means the output is not the report this
    parser was written against, so the sample fails instead of being recorded
    from whichever of the two the parser happened to read.
    """
    match = _IMPORT_LINE_RE.search(output)
    if match is None:
        raise MeasurementError("profiler output has no `import took ...` line")
    import_s = parse_duration(match.group("dur"))
    phases: dict[str, float] = {}
    for line in output.splitlines():
        row = _PROFILE_ROW_RE.match(line)
        if row is None:
            continue
        phases[row.group("name").strip()] = parse_duration(row.group("dur"))
    if "import" not in phases:
        raise MeasurementError(
            "profiler output has an `import took ...` line but no `import` row in the "
            "cumulative table, so the two statements of the import time cannot be compared"
        )
    if abs(phases["import"] - import_s) > IMPORT_CONSISTENCY_ABS_TOLERANCE_S:
        raise MeasurementError(
            f"profiler disagrees with itself: `import took` says {import_s:.6f}s while the "
            f"cumulative table says {phases['import']:.6f}s"
        )
    return (import_s, phases)


def residual_output(output: str) -> list[str]:
    """Return the lines of ``output`` that are not part of the profiler report.

    Because the profiler shares stderr with the compiler's diagnostics, "stderr
    was non-empty" cannot mean "the module is not clean" -- it is true of every
    successful run. Subtracting the report leaves exactly the diagnostics, which
    is what decides whether a timing measured real work: a module that failed to
    elaborate stops early and its ``real`` is not a build cost.
    """
    residual: list[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        if line.strip() == "cumulative profiling times:":
            continue
        if _IMPORT_LINE_RE.match(line) or _PROFILE_ROW_RE.match(line):
            continue
        residual.append(line.rstrip())
    return residual


def expand_modules(args: list[str], from_file: str | None) -> list[Path]:
    """Resolve the target module set from literal paths, globs and a list file.

    Every entry is resolved against the repository root when relative, so a run
    from any working directory selects the same files. Results are deduplicated
    **by resolved path** and sorted, which makes the sample order (and therefore
    the artifact) deterministic. Resolving before deduplicating is what makes
    the deduplication real: a pattern such as ``IsingModel/**/../*.lean`` names
    the same file once per traversed directory, and comparing the unresolved
    spellings kept all 7620 of them for 1174 distinct files -- a run 6.5x longer
    whose "median over 3 replicates" was silently a median over 19.5. A pattern
    that matches nothing, or a path that is missing or is not a ``.lean`` file,
    is an error: silently measuring a smaller set than was asked for is how a
    "family" quietly becomes three modules.
    """
    entries = list(args)
    if from_file:
        list_path = Path(from_file)
        if not list_path.is_absolute():
            list_path = REPO_ROOT / list_path
        if not list_path.is_file():
            raise MeasurementError(f"--from-file: no such file: {from_file}")
        for raw in list_path.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if line and not line.startswith("#"):
                entries.append(line)
    if not entries:
        raise MeasurementError("no target module given (pass paths, a glob, or --from-file)")

    found: set[Path] = set()
    for entry in entries:
        if any(ch in entry for ch in _GLOB_CHARS):
            base = Path(entry)
            if base.is_absolute():
                anchor = Path(base.anchor)
                pattern = str(base.relative_to(anchor))
                matches = sorted(anchor.glob(pattern))
            else:
                matches = sorted(REPO_ROOT.glob(entry))
            if not matches:
                raise MeasurementError(f"pattern matched no file: {entry}")
            found.update(match.resolve() for match in matches)
            continue
        path = Path(entry)
        if not path.is_absolute():
            path = REPO_ROOT / path
        if not path.is_file():
            raise MeasurementError(f"no such file: {entry}")
        found.add(path.resolve())

    modules = sorted(found)
    bad = [str(path) for path in modules if path.suffix != ".lean"]
    if bad:
        raise MeasurementError(f"not Lean sources: {bad}")
    return modules


def rel(path: Path) -> str:
    """Return ``path`` relative to the repository root when possible, POSIX style.

    :func:`audit_gate.rel` widened in exactly two ways this harness needs:
    ``path`` is resolved first (targets arrive as globs and as symlinked
    directories), and a path outside the repository -- an artifact written to a
    temporary directory, say -- comes back absolute instead of raising.
    """
    resolved = path.resolve()
    try:
        return _repo_rel(resolved)
    except ValueError:
        return resolved.as_posix()


def lean_options_declared() -> list[str]:
    """Return the package's ``[leanOptions]`` as ``key=value`` strings.

    Read from ``lakefile.toml`` rather than listed here, so the artifact records
    what the package actually declares on the day of the run. None of these
    options is passed to the timed child (see the module docstring): this list
    is the record of what a real ``lake build`` adds and this harness does not.
    Returns an empty list if the section is absent or the file is unreadable,
    which the artifact then shows as an empty omission list.
    """
    if not LAKEFILE.is_file():
        return []
    options: list[str] = []
    in_section = False
    for raw in LAKEFILE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("["):
            in_section = line == "[leanOptions]"
            continue
        if not in_section or line.startswith("#"):
            continue
        match = _LEAN_OPTION_RE.match(raw)
        if match is not None:
            options.append(f"{match.group(1)}={match.group(2)}")
    return options


def lean_argv(lean_bin: str, module: str) -> list[str]:
    """Return the exact child argv: bare ``lean``, profiler on, one module."""
    return [lean_bin, *LEAN_FLAGS, module]


def import_plausibility_problem(import_s: float, real: float) -> str | None:
    """Return why ``import_s`` cannot be this run's import time, or ``None``.

    The profiler's import figure is a subinterval of the process the harness
    timed, so ``0 <= import <= real`` up to the profiler's own rounding. Without
    this check a child reporting ``import took 9999s`` enters the artifact as a
    valid sample whose ``own`` is a large negative number, and the summary of a
    set containing it is not a measurement of anything.
    """
    if not math.isfinite(import_s):
        return f"import time is not finite: {import_s!r}"
    if import_s < 0.0:
        return f"import time is negative: {import_s:.4f}s"
    ceiling = real * (1.0 + IMPORT_REL_TOLERANCE) + IMPORT_ABS_TOLERANCE_S
    if import_s > ceiling:
        return (
            f"import {import_s:.4f}s exceeds the {real:.4f}s wall clock of the "
            "process that reported it"
        )
    return None


def run_capture(cmd: list[str], cwd: Path = REPO_ROOT) -> tuple[int, str, str]:
    """Run ``cmd`` and return ``(returncode, stdout, stderr)``; never raises on exit code."""
    try:
        proc = subprocess.run(
            cmd, cwd=str(cwd), capture_output=True, text=True, check=False
        )
    except OSError as exc:
        return (127, "", str(exc))
    return (proc.returncode, proc.stdout, proc.stderr)


def resolve_lean_binary(override: str | None) -> str:
    """Return the ``lean`` executable to time.

    Prefers the toolchain binary ``elan which lean`` resolves to, rather than
    the ``lean`` shim on ``PATH``: the shim re-reads ``lean-toolchain`` and
    re-execs on every invocation, adding a small constant to every sample for no
    measurement value. ``--lean-bin`` overrides; a bare ``lean`` on ``PATH`` is
    the last resort.
    """
    if override:
        return override
    code, out, _ = run_capture(["elan", "which", "lean"])
    if code == 0 and out.strip():
        return out.strip()
    return "lean"


def obtain_lean_path(override: str | None) -> tuple[str, str]:
    """Return ``(LEAN_PATH, how it was obtained)``.

    ``lake env printenv LEAN_PATH`` is run **once** for the whole measurement.
    That is the entire reason the samples are comparable to a real ``lake
    build``: paying ``lake env`` per sample is what inflated the historical
    7.0 s figure by ~1.07 s, and it is an overhead no build ever incurs.
    """
    if override:
        return (override, "--lean-path")
    code, out, err = run_capture(["lake", "env", "printenv", "LEAN_PATH"])
    if code != 0 or not out.strip():
        raise MeasurementError(
            "could not obtain LEAN_PATH from `lake env printenv LEAN_PATH` "
            f"(exit {code}): {err.strip() or out.strip()}"
        )
    return (out.strip(), "lake env printenv LEAN_PATH")


def _census_via_pgrep() -> int:
    """Count resident ``lean``/``lake`` processes with ``pgrep``; raise if it cannot."""
    total = 0
    for name in GUARDED_PROCESS_NAMES:
        code, out, err = run_capture(["pgrep", "-x", name])
        # 1 is "no match", which is an answer; anything else is a refusal to
        # answer (inside this repository's sandbox `pgrep` exits 3 with
        # "Cannot get process list", which must not read as "zero processes").
        if code not in (0, 1):
            raise MeasurementError(
                f"`pgrep -x {name}` exited {code}: {err.strip() or out.strip() or 'no output'}"
            )
        total += len([token for token in out.split() if token.strip()])
    return total


def _census_via_ps() -> int:
    """Count resident ``lean``/``lake`` processes with ``ps``; raise if it cannot."""
    code, out, err = run_capture(["ps", "-Ao", "comm="])
    if code != 0:
        raise MeasurementError(
            f"`ps -Ao comm=` exited {code}: {err.strip() or out.strip() or 'no output'}"
        )
    return len(
        [
            line
            for line in out.splitlines()
            if line.strip() and Path(line.strip()).name in GUARDED_PROCESS_NAMES
        ]
    )


def lean_process_census() -> dict[str, object]:
    """Return how many foreign ``lean``/``lake`` processes are resident, and how it was learned.

    ``{"method": str | None, "count": int | None, "error": str | None}``. The
    harness never kills anything: a foreign Lean or editor server may
    legitimately be resident, and killing a process this tool did not spawn has
    already caused real damage in this repository. What it does is *count*, so
    that the protocol's "discard any sample taken beside a non-experiment
    ``lean``" rule has an input.

    Two probes, because one of them being unavailable is not the same as the
    machine being quiet: ``pgrep`` first, ``ps`` as the fallback. If neither can
    answer, the count is ``None`` and :func:`main` refuses to measure. Recording
    ``None`` and continuing is what made the rule inert once already: the
    artifact then carries a guard field that no reader can act on, and the run
    looks compliant.
    """
    errors: list[str] = []
    for method, probe in (("pgrep", _census_via_pgrep), ("ps", _census_via_ps)):
        try:
            return {"method": method, "count": probe(), "error": None}
        except MeasurementError as exc:
            errors.append(f"{method}: {exc}")
    return {"method": None, "count": None, "error": "; ".join(errors)}


def measure_once(
    lean_bin: str,
    module: Path,
    env: dict[str, str],
    timeout_s: float,
) -> dict[str, object]:
    """Time one ``lean`` invocation on ``module`` and return the sample record.

    ``user``/``sys`` come from the ``RUSAGE_CHILDREN`` delta around the child.
    The run is serial and this process is single-threaded, so no other child is
    reaped inside the window and the delta is exactly this invocation.

    A child that cannot be spawned at all (no such ``lean``, not executable) is
    an environment error, not a slow sample: it raises
    :class:`MeasurementError` for the caller's exit-2 path rather than leaving
    an uncaught ``FileNotFoundError`` and no artifact.
    """
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    timed_out = False
    try:
        proc = subprocess.run(
            lean_argv(lean_bin, str(module)),
            cwd=str(REPO_ROOT),
            env=env,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_s,
        )
        returncode = proc.returncode
        stdout, stderr = proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        # ``subprocess.run`` has already killed and reaped the child it spawned.
        timed_out = True
        returncode = None
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
    except OSError as exc:
        raise MeasurementError(f"cannot execute lean binary {lean_bin!r}: {exc}") from exc
    real = time.monotonic() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)

    sample: dict[str, object] = {
        "module": rel(module),
        "real": round(real, 4),
        "user": round(after.ru_utime - before.ru_utime, 4),
        "sys": round(after.ru_stime - before.ru_stime, 4),
        "returncode": returncode,
        "timed_out": timed_out,
    }
    # Both streams: the profiler report is on stderr, and a diagnostic may be on
    # either, so the parse and the cleanliness check both read the union.
    combined = stdout + "\n" + stderr
    problems: list[str] = []
    if timed_out:
        problems.append(f"timed out after {timeout_s}s")
    elif returncode != 0:
        problems.append(f"lean exited {returncode}")
    diagnostics = residual_output(combined)
    if any("error:" in line for line in diagnostics):
        problems.append("lean reported an error: " + diagnostics[0][:200])
    if diagnostics:
        # Recorded, not fatal: a warning does not invalidate a timing, but it
        # must be visible in the artifact rather than absorbed into it.
        sample["diagnostics"] = [line[:200] for line in diagnostics[:5]]
    try:
        import_s, phases = parse_profile(combined)
        sample["import"] = round(import_s, 4)
        sample["own"] = round(real - import_s, 4)
        sample["phases"] = {name: round(value, 6) for name, value in sorted(phases.items())}
        # Kept in the record even when impossible -- the number is the evidence
        # of what went wrong -- but the sample stops being a measurement.
        implausible = import_plausibility_problem(import_s, real)
        if implausible is not None:
            problems.append(implausible)
    except MeasurementError as exc:
        sample["import"] = None
        sample["own"] = None
        sample["phases"] = {}
        problems.append(str(exc))
    sample["problems"] = problems
    sample["valid"] = not problems
    return sample


def summarise(values: list[float]) -> dict[str, object]:
    """Return ``median`` / ``min`` / ``max`` / ``spread`` / ``n`` for ``values``.

    No mean. The historical samples this harness replaces contain isolated
    contention blips (one 11.31 s sample among 5-7 s ones) that shift a mean and
    leave a median where it belongs; reporting both invites the wrong one to be
    quoted.
    """
    if not values:
        return {"median": None, "min": None, "max": None, "spread": None, "n": 0}
    return {
        "median": round(statistics.median(values), 4),
        "min": round(min(values), 4),
        "max": round(max(values), 4),
        "spread": round(max(values) - min(values), 4),
        "n": len(values),
    }


# Metrics summarised per module and overall. ``own`` is derived (``real -
# import``) and is listed last so a reader meets the two measured quantities
# first.
SUMMARY_METRICS = ("real", "user", "sys", "import", "own")


def summarise_samples(samples: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    """Summarise one metric per key over the *valid measurement* samples given."""
    out: dict[str, dict[str, object]] = {}
    for metric in SUMMARY_METRICS:
        values = [
            float(sample[metric])
            for sample in samples
            if sample.get("valid") and isinstance(sample.get(metric), (int, float))
        ]
        out[metric] = summarise(values)
    return out


def digest(text: str) -> str:
    """Return ``sha256:<hex>`` over ``text``, so a record can be compared without being read."""
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def git_fingerprint() -> dict[str, object]:
    """Return the git identity of the tree being measured, including *how* it was dirty.

    A bare ``dirty: true`` says the measured bytes were not ``head``'s without
    saying what they were, which leaves the measurement unattributable to any
    tree state at all. So the porcelain listing is recorded whole, together with
    a digest over it: the digest is what a re-run compares against cheaply, and
    the paths are what a reader needs when the digests differ.
    """
    code_head, head, _ = run_capture(["git", "rev-parse", "HEAD"])
    code_branch, branch, _ = run_capture(["git", "rev-parse", "--abbrev-ref", "HEAD"])
    code_status, status, _ = run_capture(["git", "status", "--porcelain"])
    dirty_paths = (
        sorted(line.rstrip() for line in status.splitlines() if line.strip())
        if code_status == 0
        else None
    )
    return {
        "head": head.strip() if code_head == 0 else None,
        "branch": branch.strip() if code_branch == 0 else None,
        # A dirty tree is not an error, but a measurement taken on one is not
        # attributable to ``head`` alone, so the artifact says which it was.
        "dirty": None if dirty_paths is None else bool(dirty_paths),
        "status_digest": digest(status) if code_status == 0 else None,
        "dirty_paths": dirty_paths,
    }


def module_digests(modules: list[Path]) -> dict[str, str]:
    """Return ``{module -> sha256}`` over the exact bytes handed to ``lean``.

    The tree's git state pins everything *except* the files a dirty tree
    changed, and those are precisely the ones a timing is most likely to be
    about. Hashing each measured module closes that gap: a later run can prove
    it measured the same source rather than assume it from a matching HEAD.
    """
    return {rel(module): digest(module.read_text(encoding="utf-8")) for module in modules}


def hardware_fingerprint() -> dict[str, object]:
    """Return what the machine is, not what this interpreter thinks it is.

    ``platform.machine()`` describes the *interpreter*: a Python running under
    Rosetta answers ``x86_64`` on Apple Silicon, which would put "x86_64" next
    to timings of a native arm64 ``lean`` in the artifact. A freshly spawned
    ``uname -m`` is not translated and reports the real architecture, so it is
    what ``machine`` means here; the interpreter's own answer and the
    translation flag are kept beside it rather than dropped, because a
    translated harness is itself worth seeing when timings look odd.
    """
    code, out, _ = run_capture(["uname", "-m"])
    native = out.strip() if code == 0 and out.strip() else None
    interpreter = platform.machine()
    model = None
    if platform.system() == "Darwin":
        code_model, out_model, _ = run_capture(["sysctl", "-n", "hw.model"])
        model = out_model.strip() if code_model == 0 and out_model.strip() else None
    return {
        "system": platform.system(),
        "release": platform.release(),
        "machine": native,
        "hw_model": model,
        "interpreter_machine": interpreter,
        "interpreter_translated": None if native is None else native != interpreter,
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
    }


def environment_fingerprint(
    lean_bin: str, lean_path: str, modules: list[Path], census: dict[str, object]
) -> dict[str, object]:
    """Return everything needed to judge, later, whether a re-run is comparable.

    ``census`` is the already-taken start-of-run process count (:func:`main`
    takes it before anything is timed and refuses to run without it), passed in
    rather than re-probed so that the number in the artifact is the number the
    guard was evaluated on.
    """
    code_version, version_out, version_err = run_capture([lean_bin, "--version"])
    version = (version_out or version_err).strip().splitlines()
    try:
        load1, load5, load15 = os.getloadavg()
        loadavg = [round(load1, 2), round(load5, 2), round(load15, 2)]
    except OSError:
        loadavg = None
    toolchain = None
    if TOOLCHAIN_FILE.is_file():
        toolchain = TOOLCHAIN_FILE.read_text(encoding="utf-8").strip()
    return {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "timestamp_local": datetime.now().astimezone().isoformat(timespec="seconds"),
        "git": git_fingerprint(),
        "lean_toolchain": toolchain,
        "lean_binary": lean_bin,
        "lean_version": version[0] if code_version == 0 and version else None,
        "lean_path_entries": len([item for item in lean_path.split(":") if item]),
        "lean_path": lean_path,
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
        "target_module_count": len(modules),
        # Total module count of the library: the dominant structural cost driver
        # here (module count x per-module fixed cost), so a later comparison can
        # tell "the family changed" from "the library grew".
        "library_module_count": len(list(LIB_DIR.rglob("*.lean"))) if LIB_DIR.is_dir() else None,
        "platform": hardware_fingerprint(),
        "loadavg_at_start": loadavg,
        "other_lean_processes_at_start": census["count"],
        # ``at_end`` is filled in by :func:`main` once the last sample is taken:
        # a process that appeared halfway through is exactly what the guard is
        # for, and only the pair of counts can show it.
        "process_guard": {
            "method": census["method"],
            "at_start": census["count"],
            "at_end": None,
            "clean": None,
            "names_counted": list(GUARDED_PROCESS_NAMES),
        },
    }


def default_out_path(label: str) -> Path:
    """Return the default artifact path, timestamped so a re-run never collides."""
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    safe = re.sub(r"[^A-Za-z0-9._-]+", "-", label).strip("-") or "run"
    return DEFAULT_OUT_DIR / f"measure-module-cost-{safe}-{stamp}.json"


def print_table(title: str, rows: list[tuple[str, dict[str, dict[str, object]]]]) -> None:
    """Print a median/spread table for the given ``(name, summary)`` rows."""
    print(title)
    header = f"  {'target':<52}" + "".join(f"{metric:>18}" for metric in SUMMARY_METRICS)
    print(header)
    for name, summary in rows:
        cells = []
        for metric in SUMMARY_METRICS:
            stat = summary[metric]
            if stat["median"] is None:
                cells.append(f"{'-':>18}")
            else:
                cell = f"{stat['median']:.2f} [{stat['min']:.2f}-{stat['max']:.2f}]"
                cells.append(cell.rjust(18))
        print(f"  {name:<52}" + "".join(cells))


def build_parser() -> argparse.ArgumentParser:
    """Return the command-line parser."""
    parser = argparse.ArgumentParser(
        description=(
            "Measure per-module Lean build cost under the canonical protocol "
            "(bare lean, one LEAN_PATH lookup, serial, discarded warm-up pass, "
            ">= 3 replicates, median + min-max spread)."
        ),
        epilog=(
            "Writes every individual sample to a JSON artifact and never deletes it. "
            "Never writes to .lake/build: lean is invoked with no output flag."
        ),
    )
    parser.add_argument("modules", nargs="*", help="module path(s) or quoted glob(s)")
    parser.add_argument("--from-file", help="file with one module path per line")
    parser.add_argument(
        "--replicates",
        type=int,
        default=MIN_REPLICATES,
        help=f"measured passes per module (minimum {MIN_REPLICATES}; default {MIN_REPLICATES})",
    )
    parser.add_argument(
        "--warmup",
        type=int,
        default=MIN_WARMUP,
        help=(
            "page-cache warm-up passes whose samples are recorded but not counted "
            f"(minimum {MIN_WARMUP}; default {MIN_WARMUP})"
        ),
    )
    parser.add_argument(
        "--label", default="run", help="short run name, used in the default filename"
    )
    parser.add_argument(
        "--out", help="artifact path (default: .self-local/reports/measure-...json)"
    )
    parser.add_argument(
        "--force", action="store_true", help="allow overwriting an existing artifact"
    )
    parser.add_argument("--lean-bin", help="lean executable to time (default: `elan which lean`)")
    parser.add_argument("--lean-path", help="LEAN_PATH override (default: `lake env printenv`)")
    parser.add_argument(
        "--timeout",
        type=float,
        default=DEFAULT_TIMEOUT_S,
        help=f"per-invocation timeout in seconds (default {DEFAULT_TIMEOUT_S:g})",
    )
    parser.add_argument("--self-test", action="store_true", help="run the harness's own test suite")
    return parser


def measure(
    modules: list[Path],
    lean_bin: str,
    env: dict[str, str],
    warmup: int,
    replicates: int,
    timeout_s: float,
) -> list[dict[str, object]]:
    """Run the warm-up and measured passes serially, returning every sample.

    Pass-major order (all modules once, then again) rather than module-major:
    any drift in machine state during the run is then spread across all modules
    instead of being concentrated in whichever module happened to be last.
    Warm-up samples are kept in the returned list, flagged ``phase="warmup"``;
    discarding them from the *statistics* is the protocol, discarding them from
    the *record* would hide exactly the cold-cache evidence a reader needs.
    """
    samples: list[dict[str, object]] = []
    passes = [("warmup", index) for index in range(warmup)]
    passes += [("measure", index) for index in range(replicates)]
    for phase, index in passes:
        for position, module in enumerate(modules):
            sample = measure_once(lean_bin, module, env, timeout_s)
            sample["phase"] = phase
            sample["pass"] = index
            sample["position_in_pass"] = position
            samples.append(sample)
            flag = "" if sample["valid"] else "  !! " + "; ".join(sample["problems"])
            imported = sample["import"]
            print(
                f"  [{phase}:{index}] {sample['module']:<62} "
                f"real {sample['real']:>6.2f}  user {sample['user']:>5.2f}  "
                f"sys {sample['sys']:>5.2f}  import "
                f"{imported if imported is None else f'{imported:>5.2f}'}{flag}",
                flush=True,
            )
    return samples


def main(argv: list[str] | None = None) -> int:
    """Run the harness and return the process exit code."""
    args = build_parser().parse_args(argv)

    if args.self_test:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from test_measure_module_cost import run_suite  # noqa: PLC0415

        return run_suite()

    # Order matters: every check that can be made from the arguments alone runs
    # before ``lake``/``elan`` are consulted. A refusal to overwrite must be
    # cheap, must not depend on a toolchain being installed, and must not first
    # spend a minute of ``lean`` on modules whose result has nowhere to go.
    try:
        if args.replicates < MIN_REPLICATES:
            raise MeasurementError(
                f"--replicates {args.replicates} is below the protocol floor of "
                f"{MIN_REPLICATES}; a median over fewer samples is not a median"
            )
        if args.warmup < MIN_WARMUP:
            raise MeasurementError(
                f"--warmup {args.warmup} is below the protocol floor of {MIN_WARMUP}; "
                "without a warm-up pass the statistics describe the page cache"
            )
        # ``float`` accepts "nan" and "inf", and both reach ``subprocess.run``
        # as a timeout it converts to an integer -- a ValueError/OverflowError
        # with no artifact and no diagnosis. A timeout is a duration or it is a
        # usage error.
        if not math.isfinite(args.timeout) or args.timeout <= 0.0:
            raise MeasurementError(
                f"--timeout {args.timeout!r} is not a positive finite number of seconds"
            )
        out_path = Path(args.out) if args.out else default_out_path(args.label)
        if not out_path.is_absolute():
            out_path = REPO_ROOT / out_path
        if out_path.exists() and not args.force:
            raise MeasurementError(f"artifact already exists (use --force): {rel(out_path)}")
        modules = expand_modules(args.modules, args.from_file)
        lean_bin = resolve_lean_binary(args.lean_bin)
        lean_path, lean_path_source = obtain_lean_path(args.lean_path)
        census = lean_process_census()
        if census["count"] is None:
            raise MeasurementError(
                "cannot count foreign lean/lake processes, so the protocol's serial-run "
                "precondition cannot be evaluated and its discard rule would be inert "
                f"({census['error']}); refusing to record the guard as unknown"
            )
    except MeasurementError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    fingerprint = environment_fingerprint(lean_bin, lean_path, modules, census)
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path

    print(f"== measure_module_cost: {len(modules)} module(s), label {args.label!r} ==")
    print(f"  lean       : {lean_bin} ({fingerprint['lean_version']})")
    print(f"  toolchain  : {fingerprint['lean_toolchain']}")
    print(f"  git HEAD   : {fingerprint['git']['head']} (dirty={fingerprint['git']['dirty']})")
    print(f"  LEAN_PATH  : {fingerprint['lean_path_entries']} entries via {lean_path_source}")
    print(f"  protocol   : bare lean, serial, {args.warmup} warm-up pass(es) discarded, "
          f"{args.replicates} replicates")
    guard = fingerprint["process_guard"]
    print(f"  other lean : {guard['at_start']} (via {guard['method']})")
    print()

    started = time.monotonic()
    try:
        samples = measure(modules, lean_bin, env, args.warmup, args.replicates, args.timeout)
    except MeasurementError as exc:
        # The child could not be spawned at all; there is nothing to write and
        # nothing partial worth keeping, so this is the environment exit.
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    elapsed = time.monotonic() - started
    census_end = lean_process_census()
    guard["at_end"] = census_end["count"]
    # Unknown at the end is not clean either: the guard is a claim about the
    # whole run, and half of it missing leaves the claim unmade.
    guard["clean"] = guard["at_start"] == 0 and guard["at_end"] == 0

    measured = [sample for sample in samples if sample["phase"] == "measure"]
    warmup_samples = [sample for sample in samples if sample["phase"] == "warmup"]
    per_module = {
        rel(module): summarise_samples(
            [sample for sample in measured if sample["module"] == rel(module)]
        )
        for module in modules
    }
    payload = {
        "schema": SCHEMA,
        "label": args.label,
        "protocol": {
            "invocation": {
                "argv": lean_argv(lean_bin, MODULE_PLACEHOLDER),
                "argv_note": (
                    f"{MODULE_PLACEHOLDER} is the absolute path of each target module; "
                    "no `lake env` wrapper, no output flag"
                ),
                # A real ``lake build`` adds the package's own options to every
                # child. This harness adds none of them, so the artifact says
                # which ones are missing instead of implying an equivalence.
                "lake_lean_options_omitted": lean_options_declared(),
            },
            "lean_path_source": lean_path_source,
            "execution": "serial (one lean process at a time)",
            "warmup_passes": args.warmup,
            "replicates": args.replicates,
            # Derived, never asserted: with ``--warmup 0`` this must read false
            # rather than describe a warm-up that did not happen.
            "warmup_samples_excluded_from_statistics": args.warmup > 0,
            "statistics": "median with min-max spread; no mean",
            "writes_build_artifacts": False,
            "timeout_s": args.timeout,
            "reference": ".self-local/reports/perf-4724-fixed-cost-reconciliation.md",
        },
        "environment": fingerprint,
        "modules": [rel(module) for module in modules],
        # The bytes actually handed to ``lean``, hashed. ``git.head`` does not
        # pin them on a dirty tree, and a dirty tree is the normal case while a
        # harness is being written.
        "module_digests": module_digests(modules),
        "wall_clock_total_s": round(elapsed, 3),
        "samples": samples,
        "per_module": per_module,
        "summary": summarise_samples(measured),
        "sample_counts": {
            "total": len(samples),
            "warmup": len(samples) - len(measured),
            "warmup_valid": len([sample for sample in warmup_samples if sample["valid"]]),
            "measured": len(measured),
            "measured_valid": len([sample for sample in measured if sample["valid"]]),
        },
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print()
    print_table("per-module medians [min-max], seconds:", sorted(per_module.items()))
    print()
    print_table("family aggregate (all measured samples):", [("ALL", payload["summary"])])
    print()
    counts = payload["sample_counts"]
    print(
        f"samples: {counts['measured_valid']}/{counts['measured']} measured valid "
        f"(+{counts['warmup_valid']}/{counts['warmup']} warm-up valid, discarded from "
        f"the statistics); wall {elapsed:.1f}s"
    )
    print(f"artifact: {rel(out_path)}")
    # Warm-up failures count. A warm-up pass that did not complete did not warm
    # the page cache, so the measured samples that follow it were not taken
    # under this protocol -- exactly the confusion the protocol exists to end.
    failed = [sample for sample in samples if not sample["valid"]]
    if failed:
        print(f"FAIL: {len(failed)} sample(s) invalid (warm-up passes included):")
        for sample in failed[:10]:
            print(
                f"  [{sample['phase']}] {sample['module']}: "
                f"{'; '.join(sample['problems'])}"
            )
    if not guard["clean"]:
        # Nothing is killed and nothing is deleted: the samples stay, and the
        # run reports that they were taken beside something else.
        print(
            f"FAIL: process guard violated (lean/lake resident: {guard['at_start']} at "
            f"start, {guard['at_end']} at end); these samples are contaminated by the "
            "protocol's own discard rule"
        )
    return 1 if failed or not guard["clean"] else 0


if __name__ == "__main__":
    sys.exit(main())
