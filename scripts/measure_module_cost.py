#!/usr/bin/env python3
"""Per-module Lean build-cost harness for the IsingModel library.

Measures what one module costs to elaborate, under the *canonical protocol* this
repository settled on in ``.self-local/reports/perf-4724-fixed-cost-reconciliation.md``
(2026-07-26, anchor ``4f9b7235``). Uses only the Python 3 standard library.

Why this exists as a script and not as prose
--------------------------------------------
Every earlier build-timing protocol here survived only as a paragraph inside a
report, and every run deleted its raw samples. The consequence was measured, not
feared: two per-module figures (~7.0 s and ~1.8 s) were carried in issue #4794 as
a "4.5x unresolved disagreement" for three days after the reconciliation report
had already explained them as a *units* mismatch, because neither figure could be
re-derived without re-inventing the protocol. A protocol that has to be
re-invented is a protocol that will differ, and two runs under different
protocols are not comparable at all.

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
summaries (median / min / max / spread / n), and an environment fingerprint
(git HEAD and dirty flag, ``lean-toolchain``, lean binary and version, target
and repository module counts, load average, timestamp). Written to ``--out``, or
to ``.self-local/reports/measure-module-cost-<label>-<timestamp>.json``. An
existing file is never overwritten without ``--force``.

Exit code 0 iff every non-warm-up sample was valid (lean exited 0 and the
profiler output parsed); 1 if any sample failed; 2 on a usage/environment error.
"""

from __future__ import annotations

import argparse
import json
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

# Repository root = parent of the ``scripts`` directory holding this file.
REPO_ROOT = Path(__file__).resolve().parent.parent
LIB_DIR = REPO_ROOT / "IsingModel"
TOOLCHAIN_FILE = REPO_ROOT / "lean-toolchain"
DEFAULT_OUT_DIR = REPO_ROOT / ".self-local" / "reports"

# Version tag of the JSON schema, so a consumer can tell two artifacts apart
# after a field is added or renamed.
SCHEMA = "ising-model/measure_module_cost/1"

# The canonical protocol's replicate floor. Enforced rather than defaulted: the
# floor is the part of the protocol that a hurried run drops first, and a
# 1-sample "median" is indistinguishable in the artifact from a 3-sample one
# unless the tool refuses to produce it.
MIN_REPLICATES = 3

# Timeout for a single ``lean`` invocation. Generous: a cold page cache has been
# observed to turn a 2 s module into a 28 s one without anything being wrong.
DEFAULT_TIMEOUT_S = 900.0

# Glob metacharacters that make an argument a pattern rather than a literal path.
_GLOB_CHARS = "*?["

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
    and sorted, which makes the sample order (and therefore the artifact)
    deterministic. A pattern that matches nothing, or a path that is missing or
    is not a ``.lean`` file, is an error: silently measuring a smaller set than
    was asked for is how a "family" quietly becomes three modules.
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
            found.update(matches)
            continue
        path = Path(entry)
        if not path.is_absolute():
            path = REPO_ROOT / path
        if not path.is_file():
            raise MeasurementError(f"no such file: {entry}")
        found.add(path)

    modules = sorted(found)
    bad = [str(path) for path in modules if path.suffix != ".lean"]
    if bad:
        raise MeasurementError(f"not Lean sources: {bad}")
    return modules


def rel(path: Path) -> str:
    """Return ``path`` relative to the repository root when possible, POSIX style."""
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.resolve().as_posix()


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


def concurrent_lean_processes() -> int | None:
    """Return how many other ``lean`` processes are running, or ``None`` if unknown.

    Best effort and *advisory only*. The harness never kills anything: a foreign
    Lean or editor server may legitimately be resident, and killing a process
    this tool did not spawn has already caused real damage in this repository.
    When ``pgrep`` is unavailable (it is, inside some sandboxes) the answer is
    ``None`` and is recorded as such, so a reader can see that the serial-run
    precondition was unverified rather than verified-clean.
    """
    try:
        proc = subprocess.run(
            ["pgrep", "-x", "lean"], capture_output=True, text=True, check=False
        )
    except OSError:
        return None
    if proc.returncode not in (0, 1):
        return None
    return len([line for line in proc.stdout.split() if line.strip()])


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
    """
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    timed_out = False
    try:
        proc = subprocess.run(
            [lean_bin, "-Dprofiler=true", str(module)],
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


def git_fingerprint() -> dict[str, object]:
    """Return the git identity of the tree being measured (HEAD, branch, dirty flag)."""
    code_head, head, _ = run_capture(["git", "rev-parse", "HEAD"])
    code_branch, branch, _ = run_capture(["git", "rev-parse", "--abbrev-ref", "HEAD"])
    code_status, status, _ = run_capture(["git", "status", "--porcelain"])
    return {
        "head": head.strip() if code_head == 0 else None,
        "branch": branch.strip() if code_branch == 0 else None,
        # A dirty tree is not an error, but a measurement taken on one is not
        # attributable to ``head`` alone, so the artifact says which it was.
        "dirty": bool(status.strip()) if code_status == 0 else None,
    }


def environment_fingerprint(
    lean_bin: str, lean_path: str, modules: list[Path]
) -> dict[str, object]:
    """Return everything needed to judge, later, whether a re-run is comparable."""
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
        "platform": {
            "system": platform.system(),
            "release": platform.release(),
            "machine": platform.machine(),
            "python": platform.python_version(),
            "cpu_count": os.cpu_count(),
        },
        "loadavg_at_start": loadavg,
        "other_lean_processes_at_start": concurrent_lean_processes(),
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
        default=1,
        help="page-cache warm-up passes whose samples are recorded but not counted (default 1)",
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

    try:
        if args.replicates < MIN_REPLICATES:
            raise MeasurementError(
                f"--replicates {args.replicates} is below the protocol floor of "
                f"{MIN_REPLICATES}; a median over fewer samples is not a median"
            )
        if args.warmup < 0:
            raise MeasurementError("--warmup must be >= 0")
        modules = expand_modules(args.modules, args.from_file)
        lean_bin = resolve_lean_binary(args.lean_bin)
        lean_path, lean_path_source = obtain_lean_path(args.lean_path)
        out_path = Path(args.out) if args.out else default_out_path(args.label)
        if not out_path.is_absolute():
            out_path = REPO_ROOT / out_path
        if out_path.exists() and not args.force:
            raise MeasurementError(f"artifact already exists (use --force): {rel(out_path)}")
    except MeasurementError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    fingerprint = environment_fingerprint(lean_bin, lean_path, modules)
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path

    print(f"== measure_module_cost: {len(modules)} module(s), label {args.label!r} ==")
    print(f"  lean       : {lean_bin} ({fingerprint['lean_version']})")
    print(f"  toolchain  : {fingerprint['lean_toolchain']}")
    print(f"  git HEAD   : {fingerprint['git']['head']} (dirty={fingerprint['git']['dirty']})")
    print(f"  LEAN_PATH  : {fingerprint['lean_path_entries']} entries via {lean_path_source}")
    print(f"  protocol   : bare lean, serial, {args.warmup} warm-up pass(es) discarded, "
          f"{args.replicates} replicates")
    others = fingerprint["other_lean_processes_at_start"]
    print(f"  other lean : {'unknown (pgrep unavailable)' if others is None else others}")
    print()

    started = time.monotonic()
    samples = measure(modules, lean_bin, env, args.warmup, args.replicates, args.timeout)
    elapsed = time.monotonic() - started

    measured = [sample for sample in samples if sample["phase"] == "measure"]
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
            "invocation": "bare lean -Dprofiler=true (no `lake env` wrapper)",
            "lean_path_source": lean_path_source,
            "execution": "serial (one lean process at a time)",
            "warmup_passes": args.warmup,
            "replicates": args.replicates,
            "warmup_samples_excluded_from_statistics": True,
            "statistics": "median with min-max spread; no mean",
            "writes_build_artifacts": False,
            "timeout_s": args.timeout,
            "reference": ".self-local/reports/perf-4724-fixed-cost-reconciliation.md",
        },
        "environment": fingerprint,
        "modules": [rel(module) for module in modules],
        "wall_clock_total_s": round(elapsed, 3),
        "samples": samples,
        "per_module": per_module,
        "summary": summarise_samples(measured),
        "sample_counts": {
            "total": len(samples),
            "warmup": len(samples) - len(measured),
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
        f"(+{counts['warmup']} warm-up discarded); wall {elapsed:.1f}s"
    )
    print(f"artifact: {rel(out_path)}")
    failed = [sample for sample in measured if not sample["valid"]]
    if failed:
        print(f"FAIL: {len(failed)} measured sample(s) invalid:")
        for sample in failed[:10]:
            print(f"  {sample['module']}: {'; '.join(sample['problems'])}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
