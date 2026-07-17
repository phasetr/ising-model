# Issue-manager triage — umbrella-detached modules (tier2 sweep2 Finding 2) — 2026-07-17

Source finding: `.self-local/reports/audit-tier2-sweep2-2026-07-17.md` Finding 2
(77 modules / 9715 lines). INDEX.md open-question row (line 132) marked this
"PENDING triage" and required a new issue + user authorization for the disposition.

## Reachability re-derivation (independent, from `IsingModel.lean` import closure)

Method: python BFS over `import` lines from the three build roots
(`IsingModel.lean`, `test.IsingModel.GKSTest`, `test.IsingModel.LeeYangTest`),
compared against every `.lean` file under `IsingModel/`.

- Total modules under `IsingModel/`: 1992
- Reachable from roots: 1912
- **Detached: 80 modules, 9893 lines** (report's 77/9715 — same order, small
  method-variance from 3 tiny re-export "aggregator stub" files (`Conditioning.lean`,
  `LatticeSystemBridge.lean`, `PseudoMass.FromParamsHZero.lean`, 8–18 lines each)
  that the report likely folded into their parent cluster row rather than counting
  as separate line items. Not a discrepancy that changes classification.)
- `lakefile.toml` confirms `lean_lib IsingModel` glob = `["IsingModel", "IsingModel.+"]`
  — **every** file under `IsingModel/` is built and CI-checked regardless of import
  reachability. Confirms the report's LOW-risk claim: wiring an already-compiling
  file is a pure additive import edge, not new elaboration; it cannot surface a
  "latent" build error that CI wasn't already catching.

## Classification (evidence: docs/index.md citation by exact filename, git log
provenance, content inspection of file headers/doc-comments, duplicate-declaration
check via repo-wide grep)

### W — keep-and-wire: 68 modules, 8312 lines

All content inspected is genuine, non-experimental GJ/FV book material or
explicitly Done-cited infrastructure. None show duplicate/superseded declarations
elsewhere in the reachable tree (verified by grep for the capstone theorem names).

| cluster | modules | lines | reason |
|---|---:|---:|---|
| `ContinuousSpin.*` (Phi4 family + TwoComponent family) | 25 | 4605 | §4.3 Thm 4.3.1 φ⁴ single-site positivity (axiom discharged, PR #3917) + §4.7 Thm 4.7.1 two-component Lebowitz (PRs #3918/#3919, **COMPLETE**) — every file cited as Done in docs/index.md:634-657 except `Measure.lean` (foundational infra for the cited files). |
| `ClusterExpansion.{MayerCore.Independent*,MayerCompleteContribution,UrsellFinThree,AlternatingFinThree,Families}` | 10 | 1377 | §18.4/§18.5 Mayer/Ursell content (PRs #3949/#3953, Issue #3954/#1499). Verified NOT superseded: `hasSum_mayerExpansionTerm_of_pairwise_disjoint` etc. exist nowhere else in the tree — report's "some superseded" hedge does not hold on inspection. |
| `Conditioning.Reflection.Euclidean{Basic,Formulas}` | 2 | 393 | GJ §10.4 reflection-positivity Euclidean inner-product lemmas (pp.198-200), explicitly doc-commented "part of the split `Conditioning.Reflection` development" — split-orphan of legitimate content, not experimental. |
| `Concrete.{Truncated2GeneralFieldCluster,Truncated2GeneralFieldDecay,CorrelationPairSymmetryBundle,CenteredSlab.InfiniteVolumeMonotone}` | 4 | 522 | §17.6.1/§17.5/§5.1 general-field decay + correlation-symmetry bundle, cited Done docs/index.md:2016 (`CorrelationPairSymmetryBundle`) and by filename for the two `Truncated2GeneralField*` rows; `CenteredSlab.InfiniteVolumeMonotone` is a split child of the cited `Concrete.CenteredSlab` β-monotonicity/positivity development. |
| `Concrete.LatticeGraphCorrelation.Lemma_17_5_2.{ChebyshevRateBridge,HasExponentialDecayChebyshev}` | 2 | 111 | §17.5 lattice Chebyshev (ℓ∞) distance, cited Done docs/index.md:1751 ("definition + 4 lemmas"). |
| `AmbientLattice.SpecialCases.{HighTemperatureBounds*×4,MagnetizationRegularityAt*×4}` | 8 | 486 | §17.6 magnetization regularity / high-temp ratio bounds — split-child wrappers (doc-commented as such) of cited parent modules; genuine theorem content, not stubs. |
| `LatticeSystemBridge.*` | 5 | 323 | Explicit Done rows docs/index.md:2048-2050 ("Done (semantic compatibility)" / "Done (additive compatibility layer)") — a deliberate additive abstraction bridge, not dead code. |
| `Peierls.{PeierlsLiminf,PeierlsMagnetizationPos}` | 2 | 141 | FV §3.7.2 Peierls capstone chain (#3631), cited Done docs/index.md:942-943. |
| `PhaseTransition.FieldResponseHighTemp` | 1 | 133 | GJ §17.6/§18.3 field-response formula via high-temp expansion, PR #3485 (real content, not yet doc-table-cited by name but not experimental/superseded). |
| `AmbientLattice.GibbsExpectationHighTempExpansion` | 1 | 61 | GJ §18.3/§18.5 along-exhaustion lift, PR #3484. Same status as above. |
| `RandomCurrent.{Switching.SwitchingIdentities,BoundedExpansion.FiniteSums(+.WeightZero)}` | 2 | 93 | GJ §5.1 Thm 5.1.2 / FV Thm 9.35 switching-lemma cardinality identities; distinct theorem names from the later SL-A/B/C/D₁ `ClusterConditioning*` chain (MEMORY) — not superseded, an earlier independent ingredient never wired. |
| `AmbientComplexAnalyticity.AscoliData.Structures` | 1 | 7 | Data-structure definitions underlying the extensively Done-cited `LeeYang*AscoliData` bridge chain (docs/index.md:603-674, §4.6 Thm 4.6.2). |

### P — keep-detached, parked (deletion forbidden without user decision): 11 modules, 1454 lines

`PseudoMass.{Composition, FromParamsBounds.{HZeroComparisons,JZeroComparisons,LogBounds,TendstoAndLower}, FromParamsHZero(+.{HZeroTruncatedBounds,JZeroBetaRegularity,JZeroHRegularity,JZeroJointRegularity,JZeroValues})}`
— Lemma 17.5.2 β-derivative programme (#2965), structurally parked (MEMORY: axioms/parked programme, "axioms keep" feedback). Zero docs/index.md citations. Leave detached, documented; no deletion without explicit user decision.

### P-test — keep-detached by design (not a parking/deletion question): 1 module, 127 lines

`IsingModel.TestGenerators` — property-test small-graph generators (Issue #888 P1),
consumed by `test/IsingModel/{Generators,SentinelProps}.lean` under the separate
`test` `lean_lib` target. Correctly NOT part of the `IsingModel` umbrella graph;
wiring it into `IsingModel.lean` would be a scope error. No action.

### D — deletion candidates: 0 modules

No module in the 80 shows the D signature (zero doc citation AND zero
mathematical-value claim AND superseded/experimental content). Every file
inspected carries a genuine GJ/FV citation in its own doc-comment header even
where docs/index.md's progress table does not separately list it by filename.
**Correction to tier2 sweep2 Finding 2**: its "some superseded by the reachable
path" hedge for the `ClusterExpansion` Mayer bits does not hold — verified no
duplicate declarations exist in the reachable tree.

## Wire plan (W class, for cycle-7 `dev-implement`/`dev-pr-clerk` — NOT executed here)

`IsingModel.lean` is a curated flat import list (492 lines, no section-umbrella
auto-transitivity for these clusters) — each of the 68 W-class leaf modules needs
its own explicit `import IsingModel.<Module>` line, inserted in the existing
section grouping (e.g. `ContinuousSpin.*` lines near existing `Concrete.*`
imports are absent entirely — a new section block would be added; `Peierls.*`/
`PhaseTransition.*`/`AmbientLattice.*`/`ClusterExpansion.*` insertions go inside
the existing contiguous import runs for those namespaces, e.g. line 128/225/241-367).

- **68 import lines**, ~9 clusters, single additive PR.
- Risk: LOW (confirmed above — glob already builds every file; wiring only adds
  a reachability edge, no new elaboration path).
- Also fold in tier2 Finding 3 (orphan split-umbrellas `MayerCore.MayerMontroll`,
  `LayerPerronExistence`) into the same PR per the report's recommendation.

## Recommendation for cycle 7

1. Wire the 68 W-class modules as **one additive PR** (dev-implement, build-arbitrated,
   within the standing B4 generic-authorization precedent — non-destructive, no math/design
   judgment beyond this triage).
2. Leave the 11 P-class (`PseudoMass.FromParams*`) modules detached, documented via
   this report; no issue action beyond noting the parked status.
3. Leave `TestGenerators` alone (correct as-is).
4. D-class: none — no user decision item to escalate this cycle.
5. Do not create a new GitHub tracking issue for this (pr-clerk's job if desired);
   this report supersedes the INDEX.md "PENDING triage" open-question row, which
   should be updated to point here.

## Addendum (2026-07-17, dev-issue-manager, cycle-7 merge-gate verification, issue #4553)

**Correction to this report's W-class claim (line 39).** The `lake build
IsingModel` cycle-7 wiring run (commit e6168ede) caught a genuine duplicate
declaration that this triage's verification method (grep spot-check for
select capstone theorem names, not a full per-declaration collision scan)
missed:

- `IsingModel.mayerExpansionTerm_eq_zero_of_no_polymers` is declared
  identically in both `ClusterExpansion/MayerCore/Truncations.lean:84`
  (this report's W-class, then-detached) and
  `ClusterExpansion/StrictPositivity/CycleSeven.lean:47` (already reachable).
- `ClusterExpansion/MayerCore/MayerTermThreeEval.lean` transitively imports
  `Truncations.lean` and is coupled to the same exclusion.

This report's line-39 statement — "Verified NOT superseded: ... exist
nowhere else in the tree" — is **retracted for these 2 of the 10
`ClusterExpansion.MayerCore.*`-cluster modules**. The other 8 modules in
that cluster are unaffected (no collision found on rebuild).

**Reclassification**: `MayerCore.{Truncations, MayerTermThreeEval}`
downgraded from **W** to **D-candidate (suspected superseded twin)**
(2 of the 10 modules / 1377 lines in that cluster).
Disposition requires a user decision (delete one twin and wire the survivor,
or keep both detached pending a dedup design) — recorded in
`.self-local/issues/4553.md` and `.self-local/issues/INDEX.md`. Not a D=0
report any more: **D = 2 modules** (was D = 0).

**Governance lesson**: grep-based "verified not superseded" checks that spot
-check only the capstone/summary theorem names of a cluster are insufficient
to rule out duplicate declarations; a full declaration-name collision scan
(or, as here, letting the compiler's `lake build` be the actual arbiter) is
required before a W-classification is final. Future triage cycles should
either run a full duplicate-declaration scan across all detached+reachable
modules before classifying, or explicitly flag W-classifications as
"provisional pending build" when only a spot-check was performed.
