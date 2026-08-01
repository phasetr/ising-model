# Tier2 repo-wide sweep #2 — 2026-07-17 (post cycles 1-5)

Main = `fe577297` (task ref `797537a1`; HEAD advanced by mirror-sync commits).
Tree: 1992 `.lean` under `IsingModel/`, umbrella root `IsingModel.lean` = 491 lines.
Method: python import-graph BFS, repo-wide token ref-count, `lake exe shake IsingModel`
(warm, exit 1, 448 residual blocks), section-boundary scan.

## Verdict
Lemma-level hygiene is CLEAN (cycle-1 #4535 worked): of 8811 named decls only **1**
ref-0 `lemma` and 4 ref-0 `def` repo-wide; the other 851 ref-0 are terminal capstone
`theorem`s (intended endpoints, consumed by docs/tex/humans not by `.lean`). No decoration
swamp remains. **Substance for a cycle-6 PR DOES exist**, concentrated in two clean,
converging, low-risk buckets: (1) a 70-file `TranslationInvariance` unused-import cluster
that shake flags with zero downstream cascade, and (2) 77 umbrella-detached modules
(9715 lines) that build via glob but are wired to no root. Everything else (oversized
files, 319 coupled shake blocks) is flag-only / FP swamp.

---

## Finding 1 [HIGH] — `IsingModel.TranslationInvariance` mass unused-import (70 files)
- Evidence: `lake exe shake IsingModel` emits **70 blocks** of `remove #[IsingModel.TranslationInvariance]`
  with **0 downstream re-imports** and **no `add`** (pure dead-import removals).
- Spot-check `IsingModel/Concrete/LatticeGraphCorrelation/Base.lean`: the string
  `TranslationInvariance` occurs ONLY on the `import` line (line 1); nothing in the body
  references the namespace. Same shape across the `Base*` family.
- These are independent leaf edits (0 downstream ⇒ no cascade, guaranteed converging).
  Phase A (#4547) missed them because it targeted umbrella→child rewrites, not
  genuinely-dead non-umbrella imports.
- Benefit: 70 real import removals, trims a hot transitive edge into the `Base*` /
  `Concrete` layer. Risk: minimal (shake-verified, no add). Recommend a scripted
  remove-then-`lake build` pass restricted to these 70.

## Finding 2 [HIGH] — 77 umbrella-detached modules, 9715 lines (build via glob, no consumer)
Not reachable from `{IsingModel.lean umbrella, GKSTest, LeeYangTest}`; 24 are in-degree 0
(imported by nothing). They still compile (lib glob `IsingModel.+`) so CI is green, but they
have no downstream consumer AND are absent from the curated umbrella. Clusters:

| lines | cluster | nature |
|------:|---------|--------|
| 4605 | `ContinuousSpin.*` (25 mod: TwoComponent Griffiths I–VII, Lebowitz, Phi4*) | φ⁴/two-component; MEMORY says §4.7 two-component is DONE+axiom-free (#3913/#3918/#3906) but continuum φ⁴ is out-of-scope. Mixed: done-work not umbrella-wired + out-of-scope stubs. |
| 1454 | `PseudoMass.FromParams*`, `Composition`, `Profile` | Lemma 17.5.2 programme (#2965), structurally parked. |
| 1377 | `ClusterExpansion.*` (MayerCore.Independent*, MayerMontroll umbrella, UrsellFinThree, AlternatingFinThree) | §18 done ingredients; some superseded by the reachable path. |
| 548  | `Conditioning.*` (Reflection.Euclidean{Basic,Formulas}, CorrelationClosed) | reflection-positivity; 40 ref-0 theorems here. |
| 523  | `Concrete.*` (Truncated2GeneralField*, CorrelationPairSymmetryBundle, Chebyshev*) | general-field decay side-branch. |
| 391  | `AmbientLattice.SpecialCases.*` (MagnetizationRegularityAt*, HighTemperatureBounds*Ferro) | |
| 323  | `LatticeSystemBridge.*` (5 mod: Abstraction, Coupling, GibbsCompat, CorrelationCompat) | abstraction bridge, no consumer. |
| 141+133+93 | `Peierls.Peierls{Liminf,MagnetizationPos}`, `PhaseTransition.FieldResponseHighTemp`, `RandomCurrent.*` | |

- Only 95 of the 856 ref-0 theorems live in these detached modules — the rest are legit
  live capstones. All 13 capstones in `capstones.txt` ARE reachable (verified: e.g.
  `mayerMontroll_coloring_identity` lives in the reachable child
  `MayerCore/MayerMontroll/EdgeInclusionExclusion.lean`).
- Benefit: deciding per-cluster (wire into umbrella vs. delete-if-superseded) removes an
  ambiguous 9.7k-line grey zone from the audit surface. Risk: MEDIUM — needs
  dev-issue-manager to confirm which clusters are done-and-parked (keep, wire to umbrella)
  vs. genuinely superseded (delete). NOT a blind-delete target. Recommend triage, not sweep.

## Finding 3 [MED] — orphan umbrella modules left by the cycle-2 split (#4538)
- `IsingModel.ClusterExpansion.MayerCore.MayerMontroll` (the aggregate created by the split)
  is imported by **nobody**; consumers import its children directly
  (`ProperColorings` / `EdgeInclusionExclusion` / `ColorClassFibre`). Same shape for the
  `LayerPerronExistence` umbrella. Both sit in `noshake.json` `ignoreAll`.
- Benefit: a split-umbrella that no one imports is dead weight; either add it to the root
  `IsingModel.lean` closure (so it earns its keep) or drop it. Risk: low. This is a
  self-inflicted post-split artifact worth cleaning while wiring Finding 2.

## Finding 4 [MED] — shake residual quality (448 blocks): partial Phase-B viable
Sampled/classified all 448:
- **FP swamp (~29)**: `remove` targets a tactic/deriving/simp transitive module
  (`Mathlib.Tactic.*`, `DeriveFintype`, positivity/ring). Already partly covered by
  `ignoreImport`; leave to noshake.
- **Genuinely applicable simple (~100)**: no `add`, ≤1 downstream. Of these **70 are the
  Finding-1 `TranslationInvariance` cluster**; the remainder are single-module leaf removes
  (`TranslationInvariance`, `AmbientLattice.CorrelationInfinite`, `Penrose.Acyclic`, etc.).
- **Coupled/medium (~319)**: umbrella→child transitive-severance chains (176 blocks have 0
  downstream but multi-module `remove` sets; 160 have exactly 1; the long tail runs to 45
  downstream re-imports on a single block). This is exactly the non-converging cascade
  Phase B (#4547) closed as unviable.
- Conclusion: a **Phase-B-lite IS worth doing** = the ~100 simple leaf edits (dominated by
  the 70 TranslationInvariance), which converge and are shake-verified. The 319 coupled
  blocks remain an FP/cascade swamp — do NOT reopen the full Phase B.

## Finding 5 [LOW] — oversized files: only 1 cleanly split-eligible
Top files by lines (>1200):
| lines | file | `/-!` sections | verdict |
|------:|------|:--:|---------|
| 1690 | `.../Lemma_17_5_2/DerivativeLimitProviderInfiniteHLS.lean` | 0 | flag-only (no boundaries) |
| 1580 | `.../Lemma_17_5_2/PseudoMassFromParamsHighTempSandwich.lean` | 0 | flag-only |
| 1481 | `.../Lemma_17_5_2/DerivativeLimitProviderFiniteHLS.lean` | 0 | flag-only |
| 1364 | `.../Lemma_17_5_2/Lipschitz.lean` | 0 | flag-only |
| 1244 | `.../Lemma_17_5_2/HLSBridgeFromSimonLieb.lean` | 7 | SPLIT-ELIGIBLE |
| 1177 | `.../Lemma_17_5_2/HLSBridgeFromCubicTanh.lean` | 12 | under 1200 |
| 1101 | `TransferMatrix/LayerOpenSpectral.lean` | 4 | under 1200 |
- Only `HLSBridgeFromSimonLieb.lean` (1244, 7 real `/-!` boundaries) is a clean split
  candidate. The four largest (1690–1364, all Lemma_17_5_2 derivative-provider files) have
  NO `/-!` section boundaries — splitting risks range/elaboration accidents; flag only.
- Note: all top files cluster in the parked `Lemma_17_5_2` (#2965) programme — low urgency.

## Finding 6 [LOW] — twins / duplicated helpers
No strong signal. Lemma-level ref graph is well-connected (only 1 ref-0 lemma repo-wide),
so α-twin duplication is not a live hot-spot. A duplicate-name scan surfaced only
structural/namespaced re-use (`Config`, `Current`, `IsEvenSubgraph`, `ReflectionPositive`)
and regex FPs (local binders), not copy-paste theorem twins. The cycle-2/5 splits did NOT
leave duplicated helper bodies across children detectably. No action.

---

## Prioritized candidates for cycle-6
1. **[HIGH] TranslationInvariance 70-file unused-import removal** — shake-verified,
   zero-cascade, converging. Highest value / lowest risk. (Finding 1 / 4)
2. **[MED] Umbrella-detachment triage** — with dev-issue-manager, classify the 77 modules
   (9715 lines) as keep-and-wire vs. superseded-delete; fold the orphan split-umbrellas
   (MayerMontroll, LayerPerronExistence) into the decision. (Finding 2 / 3)
3. **[LOW] Single split**: `HLSBridgeFromSimonLieb.lean` (1244→ along its 7 `/-!`
   boundaries) IF the Lemma_17_5_2 programme is touched; otherwise defer. (Finding 5)

Do NOT reopen full Phase-B (319 coupled shake blocks = cascade/FP swamp, already closed).
