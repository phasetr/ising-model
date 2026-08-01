# perf: H1 over-splitting import fixed-cost — VERDICT: CANDIDATE FOUND

Date: 2026-07-18. Agent: dev-perf (independent process). Read-only measurement
(3rd generic /goal re-issuance; issue-manager ruling
`issue-manager-ruling-2026-07-18-cycle10-h1.md`). Protocol reused verbatim from
#4533 (`perf-4533-m0-bottleneck-2026-07-17.md`): warm cache, AC power, single-
process `lake env lean` timing, throwaway uncommitted branch. No new ritual/
version/token invented. No source/docs committed.
**Rev 2** applies dev-review+codex findings 1-4 (`review-h1-oversplit-2026-07-18.md`);
CANDIDATE unchanged, only claim-scope/number honesty tightened.

## Preflight
- Power: `AC Power` (verified before/during/after every timed batch; charging).
- Anchor: `fe56ddf9` = `origin/main` HEAD (squash-merge of #4560 cycle-9). Local
  `main` was stale (71f79b0a); measured in detached HEAD at fe56ddf9, restored to
  `refactor/cycle-9-converging-cleanup` after.
- Machine: Apple M1 Pro (same as #4533 baseline). Toolchain unchanged.
- Working tree after experiment: only pre-existing `.self-local/issues/INDEX.md`
  (gitignored). Experiment files deleted; no commit.
- Reused rows.json (#4533, measured at f61cd03b = parent of anchor; cycle-9 delta
  = dead-twin deletion + shake, timing-negligible).
  **Disclosure (finding 4):** all 1992 rows in that rows.json carry `exit:1`
  (the sandbox `/usr/bin/time -l` failure documented in #4533 §1/F6; the `real`
  timing + `user`/`sys` CPU lines are still emitted and valid, and #4533 certified
  build cleanliness externally via a warm no-op `lake build`). The structural
  numbers cited below (subtree share, per-module user-CPU) are exit-code-robust
  and were independently reproduced from the raw file here.

## H1 mechanism
Each `.lean` module = one `lean` process that deserializes its transitive olean
closure (mathlib) before elaborating content. For a 30-line thin module this
import-load is ~all of its cost. 253 sibling modules each paying it separately is
the H1 fixed-cost tax.

## Candidate cluster
`IsingModel/AmbientLattice/SpecialCases/` = **253 modules**. Build-sum share
(rows.json): user-CPU 468s / 4565s = **10.2%**; wall 1011s / 8660s = 11.7%
(wall & CPU agree ⇒ contention-robust). 38 of the 253 are <40 lines.

Sub-family measured (self-contained): the 10 `Magnetization*` modules — shared
namespace `IsingModel.Ambient`, `open Finset Real`, external deps only
`AmbientLattice.{Defs,Exhaustion}` + internal siblings. External consumers:
3 `Concrete/LatticeGraphCorrelation/Magnetization*` + `IsingModel.lean`.

## Before/after (single-process, warm, AC) — raw: `.self-local/tmp/h1/`
BEFORE (10 separate modules), sequential elaboration (before-seq.txt):
  18.36 (cold warm-up) 7.89 8.11 6.75 7.01 6.73 8.09 6.16 6.85 7.11
  steady per-module mean 7.19s / median 7.01s; steady 10-module sum ≈ **72s**.
AFTER (10 modules merged into 1 prototype, 364 lines, unioned imports
Defs+Exhaustion, one namespace block) — after-merged.txt:
  runs 5.02 / 11.31 (contention blip) / 6.83 ⇒ mean 7.72s / **median 6.83s**.

**Reduction (finding 3):** the "~10x" compares the 10-process CPU-work-sum against
the single merged process. Exact: 72s / after ⇒ **10.5x vs median (6.83s)**,
**9.3x vs mean (7.72s, blip-inflated)**. Wall translation unchanged: the saved
~65s CPU ≈ **~6.5s wall** on the 10-core throughput-bound build. The 10 modules'
combined *content* elaboration is only ~0-2s beyond one module's fixed cost.

## Lossless-ness (finding 1 — corrected, no longer overclaimed)
The merged prototype **compiled cleanly** under `Defs+Exhaustion` only. Compile
success ≠ API preservation (unused public decls could be dropped and still
compile), so this was independently re-checked:
- BEFORE public decls (`before-decls-sorted.txt`): **15** genuine
  `magnetizationAlongExhaustion_*` theorems (a 16th regex hit was a doc-comment
  false positive: `theorem name is unchanged from the former`).
- AFTER (`after-decls-sorted.txt`): all **15/15** present; `comm -3` diff empty.
- **NOT independently verified:** per-decl type/statement equality (only names
  grep-matched), and downstream consumer re-build. Evidence:
  `.self-local/tmp/h1/decl-preservation.txt`. A real re-merge PR must diff
  signatures and rebuild the 3+1 consumers before claiming full API preservation.

## Materiality (finding 2 — regime-consistent, non-decision extrapolation)
- **Directly measured (decision-supporting):** the pilot family's ~10x
  (10.5x median) reduction, ~6.5s wall saved for this one family.
- **Extrapolation (regime-A, rows.json warm, upper-bound-leaning, NOT a decision
  fact):** SpecialCases user-CPU = 468s (10.2% of build). Merging 253 → ~25 files
  (each keeping ~1 module's fixed cost) saves ≈ **420s user-CPU ≈ ~40s wall**
  on 10 cores. As a wall fraction this is denominator-sensitive (~5% of the
  ~856s throughput-bound wall floor, up to ~9% against a user-CPU/10 floor) —
  same denominator ambiguity #4533 flagged. The earlier Rev-1 "~800s / high-
  single-digit%" mixed the pilot's fresh 7s fixed-cost (regime B) with the warm
  rows.json baseline and is retracted as optimistic. **Only the family-level 10x
  is load-bearing for CANDIDATE; the subtree number is an order-of-magnitude
  estimate, not a measured full before/after build.**

## Why this differs from #4533's NO-SELECTION
#4533 searched for a single hot MODULE (flat distribution, GraphCases only ~1%
outlier ⇒ no-selection). H1 is a different axis: aggregate per-module FIXED COST
("death by a thousand cuts"), invisible to a per-module search. #4533 itself
flagged this as hypothesis F4 ("fewer modules would cut both sum and depth"); H1
now measures it and confirms it at family scale.

## Risk / trade-off
Merging reverses deliberate cycle 1-7 splits: (a) worsens INCREMENTAL rebuild
(touching any decl rebuilds the whole merged file) — low impact here since
AmbientLattice is done/stable/rarely-edited; (b) coupled multi-file edit
(delete 10, add 1, repoint 3+1 external consumers) = out of scope for read-only
/goal, needs item-specific authorization (ruling (3)).

## VERDICT: CANDIDATE FOUND (unchanged)
File ONE item-specific issue: "Re-merge AmbientLattice/SpecialCases per-theorem
splits (pilot: 10 Magnetization* modules, measured 10.5x fixed-cost reduction) to
reclaim per-module import fixed cost." Boundary = SpecialCases subtree; pilot =
Magnetization family. STOP — no implementation, no merge, awaits explicit
item-specific auth (same gate as #4559).

Raw evidence: `.self-local/tmp/h1/{before-seq.txt,after-merged.txt,
before-decls-sorted.txt,after-decls-sorted.txt,decl-preservation.txt}`.
