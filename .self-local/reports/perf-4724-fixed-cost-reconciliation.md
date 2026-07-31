# perf #4724 — per-module fixed cost: reconciliation of measurements A and B

Date: 2026-07-26. Agent: `dev-perf` (read-only; no repo file edited, no PR).
Anchor: `4f9b7235` (main at start of run; main advanced to `5c2a4506` during the run — all
measurements were taken at `4f9b7235`).
Machine: Apple M1 Pro, 10 cores, AC power, load avg ~4 (Firefox/WindowServer background noise;
no `lean`/`lake` process running at start, verified). Single Lean process at a time except where
explicitly labelled "10-way".

## VERDICT (one line)
**Measurement A (7.0s) is inflated ~3.2x by two protocol artifacts; the confirmed per-module fixed
cost is `real` 2.22s / 2.24s CPU (warm, serial, bare `lean`), of which import = 1.68s.
Measurement B was right. But the #4563 payoff is STILL large — ~93s wall (~9%) off a clean full
build — because the fixed cost is ~100% of a SpecialCases module's cost and parallelises badly.**

---

## 1. Measurement A: source identified, protocol reconstructed

Source = `.self-local/reports/perf-h1-oversplit-2026-07-18.md` (dev-perf, 2026-07-18, anchor
`fe56ddf9`), quoted into issue #4563's body. Its protocol, as stated there:

| dimension | measurement A |
|---|---|
| tool | `/usr/bin/time` on **`lake env lean`** (per-module) |
| cache | "warm cache" (asserted), M1 Pro, AC power |
| concurrency | serial, single process |
| metric | **total `real`** of the process (NOT `real − import`) |
| target | 10 `AmbientLattice/SpecialCases/Magnetization*` modules (thin, ~30 lines) |
| replicates | 1 sweep of 10 modules for BEFORE (first run discarded as "cold warm-up" 18.36s); **3 runs** for the merged AFTER file (5.02 / 11.31 "contention blip" / 6.83) |
| headline | steady per-module **mean 7.19s / median 7.01s**; 10-module sum ≈72s; merged 6.83s ⇒ "10.5x" |

Measurement B (`perf-full-coverage-buildtime-4b14a205.md`, 2026-07-24/25, anchor `4b14a205`):
`/usr/bin/time -p lake env lean -Dprofiler=true`, serial, warm, metric split into
`own = real − import` **and `import` reported separately** (1.55–2.19s, mean ~1.8s), measured
**immediately after a clean full build had just touched every olean**.

## 2. Root cause of the 3.2–4.5x spread: YES, fully explained by protocol difference

Two independent additive artifacts, both measured directly in this run:

**(a) `lake env` wrapper overhead: +1.07s per invocation.** A real `lake build` does not pay this
(lake spawns `lean` directly); A's metric includes it, B's `import` figure does not.

```
lake env true                    real 1.10 / 1.06 / 1.07   (user 0.60)
lake env lean <empty.lean>       real 1.31 / 1.29 / 1.27
lean       <empty.lean>          (≈0.2s process start)
```

**(b) page-cache state — the dominant and highly volatile term.** `import` is mmap/page-fault
bound, not CPU bound. Same file, same tree, same session:

```
first run after other activity :  import took 11.3s   real 15.86   user 1.96   sys 3.45
runs 2-4 (page cache hot)      :  import took 1.75s   real 3.44    user 1.81   sys 1.63
```

`user` CPU is identical (1.8–2.0s) in both; only wall/`sys` explode. Re-observed at scale later in
this run: after the 10-way stress pass evicted the page cache, the first 3 serial modules measured
`import` 20s / 28.2s / 9.7s before settling back to ~1.8–2.3s. **A "warm cache" claim about
`.lake/build` says nothing about the OS page cache**, and A's own data shows the symptom it did not
diagnose: an 18.36s "cold warm-up" run, a 2.3x spread across its 10 samples (6.16–8.11), and an
11.31s "contention blip" in a 3-sample AFTER set.

A's 7.0s ≈ 1.1s (`lake env`) + a partially-cold ~5.3s import + ~0.6s init. B's 1.8s = fully-warm
import only. Both numbers are internally correct **for different metrics under different cache
states**; neither is the number a build actually pays.

## 3. Confirmed value, same protocol for both (warm, serial, bare `lean`, ≥3 replicates)

Family `PartitionFreeEnergyRegularity*` (8 modules, 399 lines; representative thin SpecialCases
family), main tree, `LEAN_PATH` from `lake env`, warm-up pass then 3 replicates × 8 modules = 24
timings. Spread was extremely tight (real 2.18–2.31 over all 24):

| metric | median | note |
|---|---|---|
| **`real` per module** | **2.22 s** | this is the per-module fixed cost |
| `import` | 1.68 s | 76% of it |
| lean init/parse/interp ("own") | ~0.55 s | ~24%; **not** content |
| `user` CPU | 1.22 s | |
| `sys` CPU | 1.02 s | mmap/page faults |
| **CPU total** | **2.24 s** | |
| + `lake env` wrapper | +1.07 s | paid by A, not by a real build |

Sampled across the whole subtree (every 8th of the 193 modules, steady-state entries): `real`
2.23–3.28, `import` 1.68–2.61, own 0.55–0.75 — **uniform**. Cross-check: a serial sweep of all 193
modules took `real` 430.29s = **2.23 s/module**, matching exactly.

**Content elaboration in this subtree is ≈ 0.** The 364-line merged file (all 8 modules' content)
costs `real` 2.53s vs 2.22s for one 30-line module — i.e. the entire family's mathematical content
is **~0.3s**, and 193 modules × 2.22s fixed ≈ 428s ≈ the measured 430.29s serial total.
**The SpecialCases subtree is ~100% per-module fixed cost.**

## 4. Direct A/B (item 4 of the brief) — DONE

Throwaway worktree `git worktree add --detach /tmp/claude-501/perf4724-wt 4f9b7235`,
`.lake/packages` symlinked to the main tree, `.lake/build` APFS-cloned (`cp -c`) so deps were warm.
Main tree's `.lake` never written. Worktree removed afterwards (`git worktree list` verified clean).

The 7 leaf modules were merged into one 364-line file (union of the 4 external imports, dependency
order preserved). **It compiles cleanly with zero errors.** Then the family's oleans/ileans/traces/
ir were deleted and `lake build <family aggregator>` timed, 3 replicates each side:

| | wall | user | sys | CPU |
|---|---|---|---|---|
| lake no-op baseline | 2.87 | 1.42 | 2.05 | 3.47 |
| **BEFORE (8 modules)** | 12.19 (11.42/12.19/19.17) | 11.85 | 12.45 | 24.30 |
| **AFTER (1 merged)** | 4.20 (4.07/4.20/4.21) | 2.97 | 2.76 | 5.73 |
| BEFORE marginal | 9.32 | | | 20.83 |
| AFTER marginal | 1.33 | | | 2.26 |

⇒ **7.0x wall / 9.2x CPU reduction** for this 8-module family; absolute saving **8.0s wall,
18.6s CPU**. A's "10.5x" *ratio* was approximately right (its 10-module family vs this 8-module
one); only its *absolute* per-module seconds were wrong.

A clean **full**-build before/after was NOT run: producing merged versions of all 28 remaining
families is an implementation task, and merging one family shifts a 17-min build by ~1s (below
noise). The subtree-scoped experiment below is the substitute, and it cross-validates against
measurement B's real full-build numbers (§5).

## 5. Scale + the parallelism correction (new finding)

All 193 SpecialCases modules, warm, `xargs -P N lean <file>`:

| concurrency | wall | user | sys | CPU total |
|---|---|---|---|---|
| serial (P=1) | 430.29 | 237.6 | 197.3 | 435 |
| **10-way (P=10)** | **121.45** (92.05 / 121.45 / 200.81) | 301–314 | **406–760** | 707–1075 |

Two consequences:
- **Parallel speedup is only 3.5x on 10 cores** (not ~7x), and running 10 Lean processes
  concurrently **inflates total CPU 1.6–2.5x, almost entirely in `sys`** (page-fault/mmap
  contention re-reading the same mathlib oleans). Import work is kernel/IO-bound and scales badly.
- Effective in-build cost per module ≈ **0.63 s wall** (121.45/193) at 10-way, range 0.48–1.04 s.

**Cross-validation with measurement B's real clean full build** (2011 modules, wall 1022s,
sum-of-module-wall 8704s ⇒ 8.5x overlap): SpecialCases' share ≈ 193 × ~4.3s = ~830s sum-wall
⇒ ~98s of real wall. Independently measured here: 121s. Agreement within the observed variance.

## 6. #4563 payoff at the confirmed value

Scope per issue #4563's 2026-07-25 correction: **193 modules total, 18/46 families done, 28
families remain** ⇒ ~175 modules in the remaining families → 28 files ⇒ **~147 modules eliminated**.

| metric | saving |
|---|---|
| CPU (serial-equivalent) | 147 × 2.24 s = **~330 s** |
| CPU (as actually incurred at 10-way, sys-inflated) | ~500–700 s |
| **clean-full-build wall** | 147 × 0.63 s = **~93 s** (range 70–150 s) |
| **as a fraction of the 1022 s clean build** | **~9 % (7–15 %)** |

### Is it worth it? **YES — this is by far the largest remaining build-time item.**
For comparison, the entire 2026-07-24/25 hot-spot campaign shipped: #4695 −7.6s, #4698 −2.4s,
#4699 −0.9s, and the two open outliers in report `4b14a205` are worth −5.3s and −4–5s. #4563 is
worth **~93s** — an order of magnitude more than all of them combined. Measurement A over-stated
the per-module cost by 3.2x, but its *conclusion* (merge the modules) survives the correction with
a large margin.

Two caveats, both of which turn out to be weaker than usually assumed:
- **Incremental-rebuild regression: empirically negligible here.** The standard objection (touching
  one decl rebuilds the whole merged file) costs 2.53s instead of 2.22s, because content ≈ 0.3s per
  family. Measured, not assumed.
- **Labour is the real cost**: 28 coupled multi-file PRs (delete N, add 1, repoint consumers,
  decl/attribute/axiom preservation gates). At ~5.3s wall saved per family this is only worth doing
  if families are **batched** (e.g. 4–7 families per PR); 28 separate PRs is a poor rate of return
  on review effort, not on build time. Standing blanket authorization already exists (#4563
  comment 2026-07-18); the batching decision is a process choice, not a perf one.

## 7. Regression prevention
- **Retire `lake env lean` real-time as a fixed-cost metric.** Use bare `lean` with `LEAN_PATH`
  from `lake env printenv LEAN_PATH`; `lake env` adds a constant 1.07s that no build pays.
- **Always warm the page cache before timing** (one discarded full pass over the target set) and
  report ≥3 replicates with the spread. A cold/partially-evicted page cache changes `import` by
  **5–15x** while leaving `user` CPU unchanged — so **report `user` CPU alongside `real`**; a large
  `real`/`user` gap is the page-cache-miss signature.
- **Beware CPU inflation under concurrency**: total CPU at P=10 is 1.6–2.5x the serial CPU for
  import-bound work. Never sum per-module CPU from a parallel build and treat it as work.
- Baseline to diff against: per-module fixed cost `real` 2.22s / import 1.68s / CPU 2.24s
  (warm, serial, bare `lean`, M1 Pro, `4f9b7235`). A drift above ~2.6s means the shared import
  closure (`AmbientLattice.Exhaustion` and friends) has grown.
- Cheap standing gate: `ls IsingModel/**/*.lean | wc -l` — module *count* is the dominant
  structural cost driver in this repo (2011 modules × ~2.2s fixed ≈ 4400s CPU ≈ 64% of the clean
  build's 6927s CPU).

## Artifacts
All ephemeral and already deleted: worktree `/tmp/claude-501/perf4724-wt` (removed via
`git worktree remove --force`, `git worktree prune` run), merged prototype `/tmp/claude-501/
merged.lean`, source backup `/tmp/claude-501/perf4724-src-bak`. No `.lean` file was written under
`.self-local/`. Main working tree untouched (`git status` clean apart from pre-existing
`.self-local/issues/{4704,4724}.md` modifications belonging to another agent).
