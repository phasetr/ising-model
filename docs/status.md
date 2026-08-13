---
layout: default
title: Current status
---

[Back to the documentation home](index.html).

## Status taxonomy

The mutually exclusive delivery statuses below apply only to the **#4787 reconciliation subset**
and the current-status ledger on this page. Legacy theorem inventories on the
[documentation home](index.html) retain historical labels such as `Done` and `Out of scope`; this
page does not normalize
those older rows.  A green build or a closed tracker is supporting evidence, not a substitute for
matching the published claim to an existing declaration.

- **Implemented:** the displayed contract is exported by the cited declarations.
- **Conditional / limited-range:** the declaration exists, but the displayed book-level headline
  is delivered only in a named parameter window, finite-volume regime, or other stated restriction.
- **Unresolved:** the displayed mathematical contract has no current declaration.
- **Deferred / not planned:** unresolved work with an explicit parking decision and reopen
  condition; this is not an implementation status.

Within that reconciliation subset, scope is recorded separately from delivery status.  In
particular, **§18.x analogy** is an orthogonal marker for the Friedli–Velenik lattice KP/Mayer
programme, not a fifth delivery status and not a claim that the row literally formalizes
Glimm–Jaffe Chapter 18.


## How to read this page

We distinguish three formalization regimes:

1. **Finite-volume** — the Ising model on a fixed finite graph
   `G : SimpleGraph ι` with `[Fintype ι]`.  Most of the project is here.
2. **Discretized infinite-volume** — a fixed finite ambient `ι` with
   growing subgraphs `G₁ ≤ G₂ ≤ ⋯`.  The "Λ ↑" convergence theorems
   of GJ §4.2 and §4.6 are formalized here: the mechanism of proof is
   identical to GJ, but the ambient lattice is finite.
3. **Genuine infinite-volume** — an unbounded ambient type `V : Type*`
   with `Λ : Finset V` finite volumes and an exhaustion `Λₙ ↑ V`.
   Introduced in `IsingModel/AmbientLattice.lean`.

When a GJ theorem is listed in the [theorem and coverage inventories](index.html) as
**Implemented**, the adjacent *Regime* column
specifies which of the three above apply.

> **Facade module notation:** The notation "(declaration-free facade; the declarations live in ...)" marks modules split in the July 2026 build-speed series (PR #4606–#4627). The absence of this notation does not indicate a module is not a facade; existing un-annotated facades are not part of that series.


## Infinite-volume status ledger

This summary keeps implemented results separate from limited contracts and unresolved book
headlines. Detailed declarations and hypotheses remain in the
[theorem and coverage inventories](index.html).

### Implemented

- **Prop. 4.6.1:** cubic-exhaustion free-energy convergence is exported by
  `Ambient.freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto`.
- **Thm. 4.6.2:** Lee–Yang-domain complex analyticity of the infinite-volume free energy is
  exported by `Ambient.freeEnergyComplex_infiniteVolume_analyticOnNhd_leeYangDomain`.
- **Prop. 5.4.2:** the canonical liminf-based `+`-boundary infinite-volume estimate is exported by
  `prop_5_4_2_plusGibbsExpectationLiminf`.
- **Lattice KP/Mayer programme:** small-activity convergence and infinite-volume free-energy
  analyticity are implemented as a lattice analogue whose primary source is Friedli–Velenik.

### Conditional / limited-range

- **§5.1 cluster property:** `clusterProperty_latticeGraph_of_polynomialDecay` assumes
  `HasPolynomialDecay`; an unconditional corollary is implemented only in the explicit
  high-temperature regime.
- **§17.8, Theorem 17.8.1 (`η ≤ 1`):**
  `correlationInfinite_polynomial_implies_exponential` proves the implication under
  `HasPolynomialDecay`.  The separate theorem
  `correlationInfinite_exponential_of_betaJ_two_d_lt_one` discharges that hypothesis only when
  `0 < J`, `0 < β`, and `βJ·2d < 1`.  This is not a continuity theorem.
- **§17.6.1, β direction:** the general-observable infinite-volume `HasDerivAt` is implemented on
  an open KP high-temperature window, not on the full book range.
- **§17.6.1, complex field:** `fieldCorrelationInfinite_latticeGraph_analytic_high_temp` gives the
  small-coupling holomorphic local-limit contract stated above.
- **§17.6.1, real reduced field:** the two
  `correlationInfinite_latticeGraph_general_*At_field_high_temp` declarations give
  general-observable differentiability for normalized `⟨a,b,1⟩`, small `a`, and
  `0 < b < r < π/2`.

### Unresolved

- **§17.5, Theorem 17.5.1:** everywhere continuity of the true `latticeMass`; the rigorous current
  capstone proves pseudo-mass continuity, the non-sharp sandwich, and true-mass continuity outside
  a countable exceptional set. No live owning GitHub issue (formerly #4788, deleted).
- **§17.6.1, β direction:** extension from the KP window to the full claimed range. No live owning
  GitHub issue (formerly #4789, deleted).
- **§17.6.1, real field residuals:** `b = 0`, arbitrary physical-parameter rescaling, the full
  nonperturbative range, and a U3/series derivative identity, sign, or uniform bound remain
  outside the implemented reduced-field theorem. No live owning GitHub issue (formerly #4790,
  closed completed — that issue tracked the finite-volume Option B capstone above, not this
  residual gap).
- **§5.1 cluster property in all pure phases:** removal of the polynomial-decay/high-temperature
  restriction. No live owning GitHub issue.

### Deferred / not planned

- No item in this reconciled subset is currently parked with a reopen condition.  A future parked
  item must name both its owning issue and that condition.

### Scope notes / analogy

- The fixed-width `K2` transfer-matrix decay results are implemented, but no separate
  “§17.8 anomalous-dimension continuity” contract is claimed: Theorem 17.8.1 is the conditional
  polynomial-to-exponential implication above.
- GJ Chapter 18 is continuum `P(φ)₂` material and is outside the literal lattice-Ising inventory.
  The project's “§18.x” entries are analogy labels for the Friedli–Velenik lattice KP/Mayer
  formalization.
- **§20.8 3D Ising roughening** is specialized interface analysis outside the current §17–18
  lattice-Ising implementation programme.


## Axioms

### Current policy: no declared project axioms

The project has no declared axioms. Representative capstones reduce only to Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

The Vitali--Porter convergence theorem
`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn` was introduced temporarily as a
function-theory axiom in PR #4234, but it has been proved from Mathlib since Issue #4280. The proof
in `ComplexAnalyticity/VitaliPorter/Theorem.lean` combines the in-project complex Montel theorem with
the identity-theorem uniqueness argument. The historical
`ComplexAnalyticity/FunctionTheoryAxioms.lean` path is now a compatibility re-export of that proved
theorem; it contains no axiom declaration.

Any future proposal for a declared axiom requires an explicit policy decision and documentation. It
must not be inferred from the historical Vitali--Porter compatibility module.

### Discharged axioms (Ising-side; all proven)

**All Ising-model axioms have been discharged** (modulo Mathlib):
`cor_4_3_3_scaled` (PR #3912) and `phi4_single_site_nonneg` (PR #3917) made GJ
§4.3 axiom-free, and the three §17.8 axioms behind `η ≤ 1` —
`ball_boundary_tight_infinite`, `shellSup_contraction`, and
`polynomialDecay_contraction_factor_tendsto` — are now all proven theorems
(`TheoremEtaLe1/`).  The general theorem remains the conditional implication
`HasPolynomialDecay → HasExponentialDecay`; only the separate slice `βJ·2d < 1`
discharges the decay hypothesis unconditionally.

`polynomialDecay_contraction_factor_tendsto` (the last declared axiom) was
**discharged as a theorem** in `TheoremEtaLe1/Contraction/Factor.lean`: the boundary edge
count obeys the *surface* bound `|latticeBallBoundaryEdges d r| ≤ 2d·|sphere_r| = O(r^{d-1})`
(`latticeBallBoundaryEdges_card_le_sphere` + `latticeSphere_card_le'`,
the sphere count via the two-to-one last-coordinate projection
`LatticeSphereCard.lean`), each endpoint sits at distance `∈ {r, r+1}` where the
polynomial-decay hypothesis (extracted from the cofinite filter) gives
`corr∞·dist^{d-1} ≤ δ`, and the volume-cancelling product
`O(r^{d-1})·O(r^{-(d-1)})·δ ≤ C·δ` is driven below any `ε`.

`shellSup_contraction` was **discharged as a theorem** in the same file: it is
the shell supremum of `ball_boundary_tight_infinite`, proved by `ciSup_le` over
the distance shell, translation invariance
(`correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant`), and the
triangle shell bound `|y−l| ≥ |y|−(r+1)` (boundary endpoints have distance
`≤ r+1`). The corrected `1 ≤ r` hypothesis (inherited from
`ball_boundary_tight_infinite`) is threaded through the contraction-factor,
high-temperature mass-gap, η≤1, and cubic-shell consumers.

`ball_boundary_tight_infinite` was **discharged as a theorem** in
`TheoremEtaLe1/BallBoundaryInfinite.lean` (infinite-volume limit of the
finite-stage `ball_boundary_simon_lieb_tight`). The formalization found the
original axiom statement false for `r = 0` (the origin lies on every boundary
edge, and the `{0,0}` Finset collapses to `⟨σ₀⟩ = 0`) and for
`latticeDistance d 0 x = r + 1` (the sink lies on a boundary edge); the proved
theorem carries the corrected hypotheses `1 ≤ r` and
`r + 1 < latticeDistance d 0 x`. The distance condition is already supplied by
the downstream `shellSup_contraction` (shell points at distance `≥ r + 2`); the
radius condition `1 ≤ r` is genuinely new and must be threaded into
`shellSup_contraction` when it is itself discharged.

The discharged GHS-corollary family (Issue #3906):
- ~~`lebowitz_third`~~: **deleted in PR #3910** — false as stated (decoupling `i` with `h > 0` forces `⟨σⱼσₖ⟩ ≤ ⟨σⱼ⟩⟨σₖ⟩`, contradicting strict GKS-II); replaced by the proven `Lebowitz.cor_4_3_4`, which is exactly `u₃ ≤ 0` (GHS) at general `h ≥ 0`
- ~~`lebowitz_four`~~: **deleted in PR #3909** — false as stated (its `h = 0` specialisation `U₄ ≤ −2⟨σᵢσⱼ⟩⟨σₖσₗ⟩` is refuted by two disjoint strongly coupled edges); replaced by the proven `Lebowitz.lebowitz_four_zero_field`
- ~~`lebowitz_inductive`~~: **discharged in PR #3911** (true as stated) — replaced by the proven `Lebowitz.lebowitz_inductive_bound` (GJ Cor 4.3.5 intermediate bound, p. 63)


## Additional axiom context

All theorems are formally proved with **zero `sorry`** and **zero declared axioms**
(modulo Mathlib's `propext` / `Classical.choice` / `Quot.sound`). Historically, a few
self-contained *complex-analysis* (function-theory) results that are out of scope for a
lattice-model library — and absent from Mathlib — were temporarily isolated as
clearly-labelled `axiom`s in dedicated modules; **all of these have since been discharged.**
The **Vitali–Porter convergence theorem** (`vitaliPorter_tendstoLocallyUniformlyOn`),
formerly such an axiom, has since been **proved from Mathlib** in
`ComplexAnalyticity/VitaliPorter/Theorem.lean` — via an in-project complex **Montel
theorem** (`VitaliPorter/MontelExtraction.lean`: Cauchy-estimate equicontinuity +
per-compact Arzelà–Ascoli over a compact exhaustion + a diagonal extraction) and the
identity-theorem **uniqueness** core (`VitaliPorter/Uniqueness.lean`) — so the
infinite-volume two-point correlation analyticity (Issue #4230, master #4214 item D) is
now **fully axiom-free** (Issue #4280). The project is now **fully axiom-free**: every
theorem reduces to `propext`, `Classical.choice`, `Quot.sound` only, with **no declared
axioms**. The last scope-excluded axiom — the **GJ §17.5 sharp-HLS derivative-limit
provider** (formerly `IsingModel.Ambient.lemma_17_5_2_derivativeLimitProvider_latticeGraph`)
— has been **discharged** (Issue #4289 / #4296): the locally-uniform convergence of the
finite-stage β-derivatives is now proven, axiom-free, on the genuine cluster-expansion
convergence window by `ConvergenceRegion.derivativeLimit_on_window`
(`ClusterExpansion/TwoPointConvergenceWindow.lean`, #4295), and the sharp-HLS capstone
`lemma_17_5_2_sandwich_sharp_cubicExhaustion` is scoped to that window
(`Icc β₁ β₂ ⊆ ConvergenceRegion.window d J`, which downcasts to `Ioo 0 (1/(J·2d))` via
`window_subset_highTemp`). This is the honest range where the cluster expansion converges;
the full formal interval `Ioo 0 (1/(J·2d))` carries no provider (no-go B2 #4269). The
sharp-HLS sandwich's *lower* side is **not** axiomatized: it is proven from an explicit
per-pair profile hypothesis (`pseudoMassG α ρ (−log(βJ·2d)) ≤ correlationInfinite {x,z}`,
the same validating-decay input the non-sharp sandwich carries), because its unconditional
`∀ x≠z` form is provably *false* (no-go B3 #4270: far pairs would force `latticeMass = ⊤`).
The Vitali–Porter axiom that previously also appeared here is now a proved theorem (#4280),
and the §17.5 derivative-limit provider axiom is now discharged (#4296), so **zero declared
axioms remain**.
`polynomialDecay_contraction_factor_tendsto` (the last Ising-side declared axiom) was
discharged as a **theorem** (`TheoremEtaLe1/Contraction/Factor.lean`): the boundary edge
count is `O(r^{d-1})` (a *surface* bound, `latticeBallBoundaryEdges_card_le_sphere`
+ `latticeSphere_card_le'`), each endpoint sits at distance `∈ {r, r+1}` where
polynomial decay forces `corr∞·dist^{d-1} ≤ δ`, and the volume-cancelling product
`O(r^{d-1})·O(r^{-(d-1)})·δ` is made small. With this, the implication in
**GJ §17.8 Theorem 17.8.1 (`η ≤ 1`) is proved under its stated
`HasPolynomialDecay` hypothesis**.  The separate high-temperature corollary discharges that
hypothesis only on the explicit `βJ·2d < 1` slice.
`shellSup_contraction` was discharged as a **theorem**
(`TheoremEtaLe1/Contraction/ShellSup.lean`) as the shell supremum of
`ball_boundary_tight_infinite` (with the corrected `1 ≤ r` hypothesis threaded
through the contraction / high-temperature / cubic-shell consumers);
`ball_boundary_tight_infinite` was discharged as a
**theorem** (`TheoremEtaLe1/BallBoundaryInfinite.lean`) — the formalization
revealed the original axiom was false for `r = 0` and for
`latticeDistance d 0 x = r + 1`, so the proved theorem carries the corrected
hypotheses `1 ≤ r` and `r + 1 < latticeDistance d 0 x` (the distance condition is
supplied by the downstream `shellSup_contraction`, whose shell points have
distance `≥ r + 2`; `1 ≤ r` must additionally be threaded into it);
the GHS-corollary Lebowitz axioms were fully discharged in PRs
#3909–#3911 (two of them were false as stated and were replaced by
corrected proven theorems), `cor_4_3_3_scaled` was proven in PR #3912
via the abstract-weight duplicate-variable layer, and
`phi4_single_site_nonneg` was proven unconditionally in PR #3917 by the
four-fold sign symmetrisation; see the *Axioms* section above.
