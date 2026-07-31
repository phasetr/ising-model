# Design: canonical protocol for "what does one additional Lean module cost" (#4794 / #4724 / #4563)

Status: DESIGN ONLY. No build was run and no code was written to produce this document.
Author: `dev-design` (independent pass). Date: 2026-07-31. Repo main at design time: `f23fa1e7`.

---

## 0. Executive finding: #4794's stated premise is false, and the real open question is different

#4794 says two measurements of *the same quantity* disagree by ~4.5x. Verified against the record,
that is not what happened.

* Figure A (7.0 s) = **total `real` of `lake env lean <file>`**, one process, partially-cold OS page
  cache (`.self-local/reports/perf-h1-oversplit-2026-07-18.md`).
* Figure B (1.55-2.19 s) = **the `import` phase only**, bare `lean`, fully warm page cache
  (`.self-local/reports/perf-full-coverage-buildtime-4b14a205.md`).

These are different quantities under different cache states. A - B is fully accounted for by two
directly measured addends: the `lake env` wrapper (+1.07 s/invocation, which a real `lake build`
never pays, since lake spawns `lean` directly) and page-cache state (same file, same session:
`import` 11.3 s cold vs 1.75 s hot, a 5-15x swing, while `user` CPU stays flat at 1.8-2.0 s). This
decomposition is recorded in `.self-local/reports/perf-4724-fixed-cost-reconciliation.md`
(2026-07-26, anchor `4f9b7235`) and was posted to both #4724 and #4563.

**Therefore: the units question is settled and does not need a new experiment to be believed.** It
is arithmetic over separately measured addends, not a contested empirical claim. #4794's framing
("mutually inconsistent measurements") is a category error that has now been carried through two
issue generations.

**The genuinely unresolved question is not the discrepancy. It is the #4563 payoff**, i.e. the one
number that actually gates the decision: *by how much does a real `lake build` get shorter if the
remaining SpecialCases families are merged?* That number **has never been measured** - it has only
ever been extrapolated. Section 2 names the specific defects that make the existing extrapolation
non-decision-grade.

Recommended disposition of #4794: **re-scope**, not "reconcile". Retitle the residual to
"measure the #4563 whole-build payoff at decision grade"; record the units reconciliation as
already answered (with the bounded re-verification of Stage 1 below as the independent check).

---

## 1. Defining the quantity (deliverable item 1)

Seven distinct things are called "per-module cost" in this repo's history. They are all real; only
one decides #4563.

| # | Quantity | Operational definition | What it is good for | Legacy figure that is this |
|---|---|---|---|---|
| Q1 | Cold full-build amortized | (clean full `lake build` wall) / (module count) | whole-repo budgeting; useless for marginal decisions (mixes content, critical path, parallel width) | measurement B's "2.0 s/module own-cost" scale check |
| Q2 | Warm serial single-module cost | `real` of bare `lean <file>` with warm `.lake` and warm page cache, one process | comparing modules to each other; regression gate on import-closure growth | the 2026-07-26 "2.22 s" |
| Q3 | Import/header overhead | the `import` phase inside Q2 | attributing cost to the import closure; target of shake / umbrella work | **measurement B (1.55-2.19 s)** |
| Q4 | **Marginal in-build cost of one extra module** | d(wall of the clean `lake build` we actually pay) / d(module count), measured as a difference between two whole-library builds | **the #4563 decision** | never measured; only extrapolated (0.63 s) |
| Q5 | olean write + read | artifact I/O inside Q2/Q4 | explains why Q3 is `sys`/mmap-bound and parallelises badly | component |
| Q6 | Process startup | `lean` on an empty file (~0.2 s); `lake env` wrapper (+1.07 s) | explains Figure A's inflation | **the +1.07 s term of measurement A** |
| Q7 | Warm incremental rebuild after a one-decl edit | edit one decl, `lake build`, wall | the cost merging makes *worse*; the trade-off side of the decision | measured only indirectly (2.53 s vs 2.22 s cold-single-module) |

**Chosen decision quantity: Q4, aggregated over the whole candidate set** - i.e. do not estimate a
per-module constant at all. Measure `T_wall(clean build, split tree) - T_wall(clean build, merged
tree)` directly on the full treatment.

Justification. Q2 and Q3 are *serial, single-process* quantities. A real `lake build` runs ~10-way
parallel, so the same work is (a) overlapped and (b) inflated in total CPU 1.6-2.5x by page-fault
and mmap contention on the shared mathlib oleans. The observed consequence is that the effective
in-build per-module cost (~0.63 s) is roughly a *third* of the serial fixed cost (2.24 s). Any
decision computed as `N x Q2` is therefore wrong by ~3.5x in the optimistic direction, which is the
same order as the "discrepancy" #4794 is worried about. Q2/Q3 are retained as **diagnostics and as
a falsifiable predictor** (Section 5), never as the decision statistic.

**Classification of the two legacy figures (deliverable item 1, reconciliation requirement):**
Figure A = Q2 + Q6(wrapper) evaluated under a partially cold page cache. Figure B = Q3 evaluated
warm. Neither is Q4. They were never measuring the same thing, so there is no winner to pick; both
are correct for their own quantity and both are unusable as a #4563 decision input.

---

## 2. Specific defects in the existing reconciliation (why it cannot simply be ratified as-is)

These are named defects, not a generic "needs review". The units analysis (Section 0) survives all
of them; the **payoff** conclusion does not.

* **D1 - Irreproducible by construction.** The report's own Artifacts section states every artifact
  was deleted: the worktree, the merged prototype, the raw timing rows. Nothing was retained under
  version control. The report's Section 7 declares a "regression-prevention gate" (drift above
  ~2.6 s) with no committed baseline data to diff against. A measurement that cannot be re-analysed
  cannot be canonical under #4794's "independently reviewed" criterion. (Figure A's raw data
  `.self-local/tmp/h1/` is likewise gone, so "reproduce both protocols" is only achievable by
  re-measuring.)
* **D2 - The decision number was extrapolated, not measured.** The headline ~93 s is
  `147 x 0.63 s`. The 0.63 s comes from `121.45 s / 193` where 121.45 is the median of an
  `xargs -P 10 lean` sweep whose three samples were **92.05 / 121.45 / 200.81 (2.2x spread)**.
  Three compounding problems: (i) `xargs -P 10 lean` is not lake's scheduler - no dependency
  ordering, no trace/olean bookkeeping, uniform concurrency; it is a surrogate for the build, not
  the build; (ii) a 2.2x-uncertain constant multiplied by 147 yields a 2.2x-uncertain headline, and
  the report's own stated range (70-150 s) is *comparable in width to the 3.2-4.5x spread it claims
  to have closed* - an inter-protocol spread was replaced by an intra-protocol spread; (iii)
  linearity in module count across 147 modules / 28 families is assumed, never tested, although
  merging changes the critical path and the available parallel width.
* **D3 - The "direct A/B" measured the wrong scope.** It deleted one family's artifacts and timed
  `lake build <family aggregator>` from an otherwise warm tree. In that scope the family *is*
  essentially the whole job and the parallel width is ~8; in a full build those 8 modules compete
  with ~1900 others for 10 cores and for page cache. The 7.0x/9.2x ratio is real for that scope and
  is not transferable to the full build. The report itself half-acknowledges this by introducing the
  0.63 s figure, but still presents the 8-module A/B as the direct evidence.
* **D4 - No negative control.** No sham A/B (two identical trees) was run, so the harness's own
  noise floor at the decision scope is unknown. Given the 2.2x spreads actually observed, this is
  not a nitpick: it is the difference between a result and an artefact.
* **D5 - n=3 with an unreported dispersion on the headline.** The BEFORE arm was
  11.42 / 12.19 / **19.17** (a 1.6x outlier). Medians of 3 under that dispersion carry a wide
  interval; no MAD or interval was reported for any headline number.
* **D6 - Anchor and denominator drift.** The report is anchored at `4f9b7235` and uses 2011 modules
  / 1022 s clean build. Today `IsingModel/` contains **1915** `.lean` files and main is `f23fa1e7`,
  with build-affecting PRs merged in between. The "~9 %" denominator has moved.
* **D7 - The incremental-rebuild trade-off is understated.** It was measured as "merged 364-line
  file 2.53 s vs single 30-line module 2.22 s" - a *cold single-module* comparison, not an
  edit-one-decl-then-`lake build` cycle including downstream invalidation. The merged module carries
  the **union** of the family's imports, so its consumers' invalidation pattern also changes.

**Net:** ratify the units decomposition; do not ratify the ~93 s payoff. Design the experiment that
measures Q4 directly.

---

## 3. Experimental design (deliverable item 2)

### 3.1 Arms

* **Control, arm S (split):** a throwaway worktree at pinned sha `BASE`, unmodified.
* **Treatment, arm M (merged):** the same worktree content with the candidate families
  mechanically concatenated - one file per family, imports = union minus intra-family edges,
  declaration order preserved, consumers repointed. Built as a **measurement prototype**, not a PR:
  it must compile warning-free and preserve the declaration name+type set, but it is not required to
  satisfy PR-grade review or docs/tex sync.

### 3.2 Held fixed

Pinned sha; `lean-toolchain` (`leanprover/lean4:v4.29.0`) and `lake-manifest.json` byte-identical
across arms; `.lake/packages` (mathlib oleans) **shared by symlink** from the primary tree and never
rebuilt; lakefile options (`warningAsError = true`, `maxSynthPendingDepth = 3`, etc.); machine, AC
power, thermal state; declaration name+type set (verified mechanically); `#print axioms` output.

### 3.3 Scopes measured

* **S-scope (subtree, cheap, ~2 min/build).** Delete the IsingModel artifacts for the
  `AmbientLattice/SpecialCases` closure only, then build that closure's aggregator. Used for
  screening, for the Magnetization reverse check, and to derive the *prediction* fed into F-scope.
* **F-scope (whole library, decision grade, ~17 min/build).** `rm -rf` the IsingModel half of
  `.lake/build` (mathlib artifacts untouched), then `lake build`. **Only F-scope results may be used
  for a GO decision.**

### 3.4 The confound that merging changes more than module count

Merging simultaneously changes (a) module count, (b) import-graph shape (consumers now transitively
import the union closure), and (c) available parallel width / critical-path length. These are **not
separable confounds - they are constituents of the treatment effect**, and that is exactly why the
decision metric must be a whole-build wall difference rather than a per-module constant: the full
build automatically prices all three. The design therefore does not try to control them; it
*records* them as covariates so a reviewer can see which mechanism dominated:

* transitive import-closure size of each affected consumer, both arms (static, cheap);
* dependency depth (longest chain) of the SpecialCases subtree, both arms;
* observed peak concurrent `lean` processes, sampled every 2 s during each build.

A change in peak concurrency between arms is **reported, not discarded** - at F-scope it is part of
the effect. For the Q2/Q3 serial diagnostics, concurrency is forced to 1 and any deviation voids the
sample.

### 3.5 Order and pairing

Paired ABBA scheduling, never all-S-then-all-M (page cache and thermal state drift monotonically
within a session). F-scope order: `[warm-up S] S M M S S M`. Analysis is on **per-pair
differences**, plus a sign test across pairs.

### 3.6 The Magnetization pilot named in #4794 - executable substitute

#4794 requires re-measuring the Magnetization pilot. **That family no longer exists**: commit
`fa163e07` (PR #4564) merged the 10 modules into one 279-line file, which `git log` shows has not
been modified since. The criterion is therefore unexecutable as literally written.

Substitute, and it is *stronger* than a fresh prototype because the merged arm is the shipped
artifact rather than a mock-up: run a **reverse-direction A/B at S-scope**.

* Arm M = today's tree, unmodified.
* Arm S = restore the 10 leaf files from `fa163e07^` via `git show fa163e07^:<path>`, and replace
  `SpecialCases/Magnetization.lean` with a pure re-export umbrella importing those 10 leaves.
* Rationale for the umbrella variant: it keeps today's 4 consumers
  (`IsingModel.lean` + three `Concrete/LatticeGraphCorrelation/Magnetization*`) **byte-identical**,
  so the treatment is isolated to the family itself. Deviation from history to be recorded: the
  split arm has 11 modules, not the historical 10, and one extra import hop. The historical variant
  (consumers repointed to the 10 leaves, from `fa163e07^`) is optional and only if those consumers
  have not drifted.
* Pre-check: the declaration name+type set of the 10 restored leaves must equal that of today's
  merged file; if not, the reconstruction is not content-faithful and this arm is dropped.

### 3.7 Sample sizes

S-scope: 1 discarded warm-up + **7 paired replicates** per arm. F-scope: 1 discarded warm-up +
**3 paired replicates** per arm. Serial diagnostics (Q2/Q3): >= 16 modules drawn from >= 2 families,
x 3 replicates (>= 48 timings). Sham/negative control: 7 pairs at S-scope, 1 pair at F-scope.

---

## 4. Confound control (deliverable item 3)

### 4.1 Cache state discipline

Three independent caches; each needs its own reproducible reset.

1. **mathlib oleans (`.lake/packages`)** - always warm, never rebuilt, shared read-only by symlink.
   Assert `lake-manifest.json` hash equality before and after every stage.
2. **IsingModel artifacts (`.lake/build/lib/lean/IsingModel/**`)** - the manipulated variable.
   * *Reach "warm/no-op"*: run `lake build` on the primary tree until it is a genuine no-op, then
     snapshot `.lake/build` and APFS-clone it (`cp -c`) into each worktree.
     **This is currently required before anything else**: the primary `.lake/build` is not no-op
     (olean mtimes predate source mtimes) and the OS page cache is cold after ~19.5 h idle.
   * *Reach "cold-for-IsingModel"*: `rm -rf` exactly that subtree, never touching `.lake/packages`.
   * *Verification that the reset worked*: count the modules lake actually rebuilds (job count in
     `lake build` output, or count oleans with mtime newer than a marker file) and assert it equals
     the expected value for the arm. Arm M rebuilding ~1900 modules at S-scope means the reset or
     the clone leaked; sample void.
3. **OS page cache** - the dominant volatile term (5-15x on `import`) and the one that destroyed
   Figure A. It cannot be flushed selectively on macOS (`purge` is global, needs sudo, and would
   evict mathlib - which is *not* what a real build sees).
   **Decision: standardise on WARM page cache.** Reached by a mandatory discarded warm-up replicate
   per arm immediately before the recorded replicates. The cold-page-cache regime is declared
   explicitly **out of scope**; this protocol answers for the warm local/CI-with-cache steady state
   only, and that limitation is to be restated in any report using its numbers.
   *Detection of a page-cache miss inside a supposedly warm sample*: `real` >> `user + sys`. A
   pre-declared band is used as a discard rule (Section 4.4).

### 4.2 Worktree and primary-cache isolation

`git worktree add --detach "$TMPDIR/perf4794-<arm>" <BASE>`; `.lake/packages` symlinked to the
primary tree; `.lake/build` APFS-cloned from the pristine snapshot. **Post-condition check
(mandatory, was only informal previously):** `find <primary>/.lake -newer <marker-file>` must return
nothing except `.lake/packages` reads; if the primary `.lake/build` was written, the whole stage is
void and the primary tree must be re-warmed. Worktrees removed with `git worktree remove --force` +
`git worktree prune` at the end, verified by `git worktree list`.

### 4.3 Process isolation and machine-load guard

* Exactly one experiment at a time, enforced by a lockfile; no other agent may build concurrently.
* **A foreign `codex` process is resident and must never be killed.** Record its pid and `%cpu` at
  the start and end of every replicate; do not signal it. Prior sessions caused real harm with broad
  `pkill`; broad pattern kills are forbidden by this protocol.
* Lake 5.0.0 has **no `-j`/`--jobs`** flag, so build parallelism cannot be capped. Consequences:
  (i) F-scope builds run at lake's native ~10-way and that is *correct* for the decision metric;
  (ii) the Q2/Q3 serial diagnostics must therefore bypass lake and invoke bare `lean` one process at
  a time with `LEAN_PATH` obtained once from `lake env printenv LEAN_PATH`;
  (iii) never run two stages concurrently to "save time".
* Pre/post guard per replicate: 1-minute load average < 2.0 (10-core M1 Pro); zero non-experiment
  `lean`/`lake` processes; AC power (`pmset -g batt`); no thermal throttle
  (`pmset -g therm`, `CPU_Speed_Limit == 100`).
* **Tooling note:** `/usr/bin/time -l` fails in this sandbox (`sysctl kern.clockrate`) and a prior
  protocol lost every row to exit=1 that way. Use `/usr/bin/time -p` (or bash `time`) and assert the
  timing row parsed non-empty before accepting a sample.

### 4.4 Contaminated-sample detection (pre-declared discard rules)

Discard, and *replace*, any sample where: (1) any guard in 4.3 fails at start or end; (2) foreign
`codex` mean `%cpu` > 25 %; (3) a non-experiment `lean`/`lake` process was observed; (4) for serial
diagnostics, `real > 1.6 x (user + sys)` (page-cache-miss signature); (5) the rebuilt-module count
does not match the arm's expectation; (6) wall > median + 3 x MAD of that arm.

Discarded samples are **logged, never silently dropped**; the report states the discard count. If
more than 30 % of samples in a stage are discarded, the stage is declared failed and escalated -
it is not patched up by taking more samples until enough survive.

---

## 5. Statistics and the pre-registered decision rule (deliverable item 4)

### 5.1 Statistic

**Median** of per-pair differences, not mean: build times are right-skewed with rare ~2x contention
outliers (11.42/12.19/**19.17** is the documented example), and the mean is not robust to them.
Report for every arm and every scope: n, all raw samples, median, **MAD**, min, max, discard count,
and `user`/`sys` CPU alongside wall (the page-cache signature). Report the paired-difference median
and the sign test across pairs.

### 5.2 Pre-registered decision rule for #4563

To be committed to git **before** the first Stage-2 sample is taken; review must verify that the
commit timestamp precedes the raw-log timestamps.

* **GO** (recommend the SpecialCases re-merge to the user, batched 4-7 families per PR) requires
  **all** of:
  1. F-scope median paired Delta >= **45 s** and >= **4.5 %** of median `T_split`;
  2. all 3 F-scope paired differences positive (3/3 sign test);
  3. F-scope sham (negative control) median |Delta| < **15 s**;
  4. Q7 incremental-edit regression <= **1.0 s** per touched family (measured, not assumed);
  5. merged prototype builds warning-free, declaration name+type set identical, `#print axioms`
     unchanged, `lake exe shake` introduces no new unused import.
* **NO-GO** (recommend closing #4563/#4794 as not worth doing) if **any** of: F-scope median
  Delta < **15 s**; or < **1.5 %** of `T_split`; or fewer than 3/3 paired differences positive; or
  Q7 regression > **2.0 s** per family.
* **INCONCLUSIVE** (Delta in [15 s, 45 s)): **this is not a GO.** Escalate to the user with the raw
  numbers and two options: raise n to 5 F-scope pairs, or restrict the scope to the largest families
  only. No implementation may start from an INCONCLUSIVE result.

**Why 45 s.** Two independent arguments converge. (i) The existing extrapolation predicts ~93 s
(range 70-150 s); setting the bar at roughly half the point prediction leaves the experiment
genuinely able to fail while still being clearable if the prediction is even approximately right.
(ii) The entire preceding hot-spot campaign shipped -7.6, -2.4, -0.9, -11.5, -22.1, -3.3 s
= **~48 s summed**. Requiring #4563 to be worth about as much as an entire prior campaign is the
right bar for 28 coupled multi-file PRs, each carrying declaration/attribute/axiom preservation
risk. **Why 15 s for NO-GO:** below ~1.5 % of a clean build, the aggregate payoff does not justify
the review risk of coupled deletions, and it is at the edge of the harness noise floor.

**Evidential asymmetry (deliberate).** GO requires the sham control to have passed; NO-GO does not.
Action requires stronger evidence than inaction: a NO-GO leaves the repo untouched, so a
noise-inflated NO-GO costs only a missed optimisation, whereas a noise-inflated GO buys 28 risky PRs.

**Anti-rationalisation clause.** Thresholds, scopes, and discard rules may not be edited after any
Stage-2 sample exists. If the result is disliked, the permitted response is a *new*, separately
pre-registered experiment - not a re-reading of this one.

### 5.3 Pre-registered model-falsification test

Before F-scope runs, state the prediction `Delta_F_pred = N_eliminated x c`, where `c` is the
in-build marginal per-module cost derived from the S-scope result and `N_eliminated` is the
fail-closed module count from Stage 0. After F-scope, report `Delta_F_measured / Delta_F_pred`. If
that ratio falls outside **[0.5, 2.0]**, the linear per-module cost model is **REFUTED** and must be
reported as refuted - including when the measured value is *better* than predicted. This is the
clause that makes the whole exercise falsifiable rather than confirmatory.

---

## 6. Staging, cost, and the bounded pilot (deliverable item 5)

### Stage 0 - Harness, enumeration, negative control (~1 h machine)

* Warm the primary tree to a genuine `lake build` no-op; snapshot `.lake/build`.
* **Fail-closed family enumeration**: assign every one of the 193 `SpecialCases` modules to exactly
  one family or to an explicit "not mergeable" bucket; assert the partition sums to **193**. Any
  unassigned module aborts the stage. (Indicative, must be re-derived, not trusted: the largest live
  prefixes are `PartitionFreeEnergy*` ~19, `MayerVd*` ~12, `Susceptibility*` ~9, `Joint*` ~8. The
  "28 families / ~175 modules / 147 eliminated" figures inherited from #4563 are themselves
  unverified at today's main and must be re-derived by this step.)
* **Sham A/B**: two identical worktrees, S-scope, 7 pairs. Gate: median |Delta_sham| < 15 s,
  otherwise the harness cannot resolve the decision and all downstream stages are void.

### Stage 1 - Bounded re-verification of the 2026-07-26 numbers at today's main (~30 min machine)

This is the **minimum bounded re-verification** answering "is the units question settled at today's
main", and it is small enough to run in a single session on its own.

* Q2/Q3 by the unified protocol (warm, serial, bare `lean`, `LEAN_PATH` from
  `lake env printenv LEAN_PATH`, `/usr/bin/time -p`), >= 16 modules x 3 replicates.
  **Pre-registered ratification band:** `real` median in **1.67-2.78 s** (2.22 +/- 25 %) and
  `import` median within **1.18-2.18 s** (1.68 +/- 30 %). Inside band -> the 2026-07-26 measurement
  is independently ratified at today's main and #4724's units question is formally closed. Outside
  band -> report the drift and its direction; a `real` median above 2.6 s specifically corroborates
  that report's own stated prediction that the shared import closure has grown.
* Reproduce protocol A cheaply, closing #4794's "reproduce both protocols" without the deleted raw
  data: `lake env true` x 5 (expect ~1.07 s) and the same module under `lake env lean` vs bare
  `lean` x 3 (expect a ~1.07 s constant offset).

### Stage 2 - The decision experiment (~3-3.5 h machine + prototype construction labour)

* Build the merged prototype for **all live candidate families** (scripted concatenation + consumer
  repoint), iterating until warning-free. Budget 2-3 debug builds.
* Magnetization reverse A/B (Section 3.6), S-scope, 7 pairs (~30 min).
* S-scope A/B on the full prototype, 7 pairs (~35 min). Derive `c`; **write down `Delta_F_pred`**.
* F-scope A/B, 3 pairs + warm-up = 7 clean builds (~2 h).
* F-scope sham, 1 pair (~35 min) - mandatory for a GO.
* Q7 incremental-edit regression: >= 4 families x both arms x 3 replicates (~20 min).

**Total: roughly 5 h machine time plus prototype-construction labour.** That is affordable and there
is no need to degrade the design - but it does not fit a single short session, so Stage 1 is
explicitly separable and should be run first.

### Bounded pilot (if the full prototype cannot be made to compile within budget)

Treatment restricted to the four largest live families (indicatively 19 + 12 + 9 + 8 = 48 modules
-> 4 files, ~44 eliminated, ~30 % of the inherited 147) plus the Magnetization reverse check.
S-scope 7 pairs + F-scope 2 pairs.

* **What the pilot CAN conclude:** whether Q2/Q3 hold at today's main; the *sign* and S-scope
  magnitude of the merge effect; whether the linear per-module model survives its own prediction
  test at 30 % scope; whether Q7 regression is real.
* **What the pilot CANNOT conclude, and must not be reported as concluding:** a GO. Scaled
  proportionally, the pilot's GO-equivalent F-scope threshold is `45 x 44/147 ~ 13.5 s`, which sits
  *at or below the sham noise floor*. **A bounded pilot is therefore structurally incapable of
  authorising #4563**; only the full-set treatment can. It also cannot say anything about modules
  outside `SpecialCases` - matching #4794's own "do not generalize pilot results to unmeasured
  modules" criterion.

---

## 7. Committed tooling (so this is not re-derived a fifth time)

Every past protocol survives only as prose in a report; `scripts/` currently holds audit scripts
only, with no timing target. Recommend committing a small, re-runnable harness:

* `scripts/perf/guard.sh` - pre/post environment guard; emits one JSON row (load1, thermal state, AC
  status, `lean`/`lake` process count, foreign `codex` pid and `%cpu`, git sha, `lean-toolchain`,
  `lake-manifest.json` hash, lake version). Non-zero exit on any violation.
* `scripts/perf/module_cost.sh <module-list> <reps>` - Q2/Q3: warm, serial, bare `lean`,
  `LEAN_PATH` from `lake env printenv LEAN_PATH`, `/usr/bin/time -p`, one JSON row per sample
  (real/user/sys/import/own).
* `scripts/perf/ab_build.sh <arm-label> <scope:subtree|full> <reps> <schedule-file>` - artifact
  reset, warm-up discard, ABBA order from the schedule file, peak-`lean`-concurrency sampling,
  rebuilt-module-count assertion.
* `scripts/perf/analyze.py` - reads the raw rows, emits n / median / MAD / min / max / discards, and
  **evaluates the pre-registered rule mechanically**. A reviewer re-runs this on the committed raw
  rows and must obtain the report's headline without trusting the report's tables.

**Data-retention rule (the fix for D1).** Raw rows go to `.self-local/perf/4794/raw/` and the merged
prototype is retained as a **`.patch` file only**. Note that `.self-local` is globally gitignored,
so retained data must be **force-added** (`git add -f`) to be durable and reviewable - otherwise
this repeats D1 exactly. **Never** retain a compilable `.lean` under `.self-local` (a tracked `.lean`
placed there previously left main red for 2 commits, #4718).

---

## 8. Failure modes and falsifiability (deliverable item 6)

The historical failure mode is specific: build-speed opportunity was declared "exhausted" three
times and was wrong all three times, because *static inventory was trusted over measurement* and
because the completion claim carried no test that could fail. The same pattern produced the "tex
dangling" defect that recurred four times, where a scan issued an exemption and declared itself
complete. The countermeasures below are designed against that pattern specifically.

| # | Countermeasure | What it catches |
|---|---|---|
| F1 | **Pre-registered prediction + [0.5, 2.0] refutation band** (5.3), stated before F-scope runs | a headline reconciled after the fact to whatever was measured |
| F2 | **Negative control / sham A/B** (Stage 0), mandatory for a GO | the harness measuring its own noise and calling it an effect - the gap that D4 left open |
| F3 | **Retained, force-added raw data + a reviewer-runnable analyzer** (Section 7) | D1: an unfalsifiable report; a reviewer who can only re-read prose |
| F4 | **Fail-closed family enumeration summing to 193** (Stage 0) | a scan that "completes" by quietly excluding items - the recurring exemption-as-completion defect |
| F5 | **Discard rules pre-declared, discards counted and reported, >30 % = stage failed** (4.4) | sampling until the desired answer survives |
| F6 | **Both directions reported (Q4 payoff *and* Q7 regression), with Q7 in the GO conditions** | optimising the metric that was measured while silently degrading the one that was not |
| F7 | **Every number carries its measured scope**; per-module constants may never be multiplied out beyond the measured set without the F1 test | D2/D3: extrapolation presented as measurement |
| F8 | **Covariates recorded** (import-closure size, subtree depth, peak concurrency) | a correct Delta with the wrong causal story, which then mis-guides the next campaign |

**What would make this protocol itself wrong.**

1. *Warm-page-cache standardisation is a scope choice, not a truth.* If the objective is CI cold
   builds (`lean_action_ci.yml`), these numbers do not transfer. The protocol answers for the warm
   local steady state and says so; a cold-cache answer needs a different, and much noisier, design.
2. *Clean-full-build wall may not be the right objective at all.* Developers mostly pay Q7, not Q4.
   If Q7 dominates real cost, merging is neutral-to-harmful and the whole framing is wrong. This is
   why Q7 sits inside the GO conditions rather than in a caveat paragraph.
3. *APFS-clone artifact reuse may leave lake's trace/mtime bookkeeping in a state that differs from a
   genuine cold start.* Guarded by the rebuilt-module-count assertion (4.1); if that assertion cannot
   be made to hold, fall back to real `rm -rf` + full rebuild and accept the extra wall time.
4. *Content drift mid-experiment.* All stages are pinned to one sha; toolchain and manifest hashes
   are asserted per replicate. If main advances during the run, that is recorded, not absorbed.
5. *The prototype is not the PR.* A mechanically concatenated prototype may be faster than the
   PR-grade merged code that would actually ship (or slower). The GO decision therefore authorises a
   **first batch with post-merge re-measurement**, not the whole 28-family campaign unmeasured.

---

## 9. PR / work decomposition (logical units, not per-function slices)

1. **PR-1 - measurement harness + pre-registration.** `scripts/perf/{guard,module_cost,ab_build}.sh`
   + `analyze.py`, plus this protocol and the pre-registered thresholds committed. No results yet.
   This PR is what makes every later claim checkable.
2. **PR-2 - Stage 0 + Stage 1 results.** Fail-closed family enumeration, sham control, Q2/Q3
   re-verification at today's main, protocol-A reproduction. Disposition of the *units* question
   (#4724) posted to #4794 with raw data attached. Runnable on its own in one session.
3. **PR-3 - Stage 2 results.** Prototype `.patch`, S-scope + F-scope + Magnetization-reverse + Q7
   raw data, mechanical evaluation of the pre-registered rule, GO/NO-GO/INCONCLUSIVE disposition.
4. **PR-4+ - implementation, only on GO and only with the user's explicit authorisation.** First
   batch of 4-7 families, then **re-measure** before continuing (Section 8 item 5).

## 10. Open items requiring the main agent / user (not decidable here)

1. **#4794's disposition.** Its premise is false as written (Section 0) and its named pilot family
   no longer exists (Section 3.6). Re-scoping the issue is a governance act, not a design act.
2. **Authorisation.** #4563's standing blanket authorisation has no verifiable primary-source user
   utterance and has been dormant since 2026-07-19. Even a GO here does not authorise
   implementation.
3. **Budget.** Full protocol ~5 h machine time plus prototype labour, versus a ~1.5 h bounded pilot
   that is structurally incapable of producing a GO. Which to run is a user call.
4. **Whether Q4 or Q7 is the objective.** If the user's real complaint is edit-rebuild latency rather
   than clean-build wall, the SpecialCases merge is arguably the wrong intervention entirely and the
   experiment should be re-aimed before it is run.
