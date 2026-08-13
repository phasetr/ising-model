---
layout: default
title: Current status
---

[Back to the documentation home](index.html).

## Status taxonomy

The mutually exclusive delivery statuses below apply only to the **#4787 reconciliation subset**
and the current-status ledger on this page. Legacy rows in the
[theorem catalogue](theorems/index.html) and
[book-coverage inventory](coverage/index.html) retain historical labels such as `Done` and
`Out of scope`; this page does not normalize those older rows. A green build or a closed tracker is
supporting evidence, not a substitute for matching the published claim to an existing declaration.

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

When a GJ theorem is listed in the [theorem catalogue](theorems/index.html) or
[book-coverage inventory](coverage/index.html) as
**Implemented**, the adjacent *Regime* column
specifies which of the three above apply.

> **Facade module notation:** The notation "(declaration-free facade; the declarations live in ...)" marks modules split in the July 2026 build-speed series (PR #4606–#4627). The absence of this notation does not indicate a module is not a facade; existing un-annotated facades are not part of that series.


## Infinite-volume status ledger

This summary keeps implemented results separate from limited contracts and unresolved book
headlines. Detailed declarations and hypotheses remain in the
[theorem catalogue](theorems/index.html) and
[book-coverage inventory](coverage/index.html).

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
  small-coupling holomorphic local-limit contract recorded in the
  [theorem catalogue](theorems/index.html) and
  [book-coverage inventory](coverage/index.html).
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
  closed completed — that issue tracked the finite-volume Option B capstone recorded in the
  [theorem catalogue](theorems/index.html) and
  [book-coverage inventory](coverage/index.html), not this residual gap).
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

### Current snapshot

The project has no declared axioms. Representative capstones reduce only to Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

The Vitali--Porter convergence theorem
`IsingModel.FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn` is proved from Mathlib by the
in-project complex Montel theorem and identity-theorem uniqueness argument. The historical
function-theory-axiom module is now a compatibility re-export of that proved theorem; it contains
no axiom declaration.

Any future proposal for a declared axiom requires an explicit policy decision and documentation. It
must not be inferred from the historical Vitali--Porter compatibility module.

### Implementation landmarks

- **Vitali--Porter.** The temporary function-theory axiom has been replaced by a proof in
  `ComplexAnalyticity/VitaliPorter/Theorem.lean`, assembled from the Montel extraction in
  `ComplexAnalyticity/VitaliPorter/MontelExtraction.lean` and identity-theorem uniqueness in
  `ComplexAnalyticity/VitaliPorter/Uniqueness.lean`. The historical module
  `ComplexAnalyticity/FunctionTheoryAxioms.lean` remains only a compatibility re-export.
- **Sharp-HLS derivative provider.** `ConvergenceRegion.derivativeLimit_on_window` is proved in
  `ClusterExpansion/TwoPointConvergenceWindow.lean` only on `ConvergenceRegion.window d J`; there
  is no provider for the full formal high-temperature interval. The sharp lower sandwich still
  requires the explicit per-pair profile hypothesis
  `pseudoMassG α ρ (−log(βJ·2d)) ≤ correlationInfinite {x,z}`.
- **GJ §17.8.** The three former Ising-side axioms are theorems, but the capstone remains the
  conditional implication `HasPolynomialDecay → HasExponentialDecay`; only the separate
  `βJ·2d < 1` slice discharges decay unconditionally. The corrected boundary theorem requires
  `1 ≤ r` and `r + 1 < latticeDistance d 0 x`; the old statement failed at `r = 0` and at
  `latticeDistance d 0 x = r + 1`. Its live owners are
  `Concrete/LatticeGraphCorrelation/TheoremEtaLe1/Contraction/Factor.lean`,
  `Concrete/LatticeGraphCorrelation/TheoremEtaLe1/Contraction/ShellSup.lean`,
  `Concrete/LatticeGraphCorrelation/TheoremEtaLe1/BallBoundaryInfinite.lean`, and
  `Concrete/LatticeSphereCard.lean`.
- **GHS/Lebowitz replacements.** `lebowitz_third` and `lebowitz_four` were false as stated and
  replaced by the proved `Lebowitz.cor_4_3_4` and `Lebowitz.lebowitz_four_zero_field`;
  `lebowitz_inductive` was true as stated and is discharged by
  `Lebowitz.lebowitz_inductive_bound`. The source owners are
  `Inequalities/Lebowitz/Cor434.lean`, `Inequalities/Lebowitz/LebowitzFour.lean`, and
  `Inequalities/Lebowitz/Cor435.lean`.
- **Remaining Ising and continuous-spin discharges.** `cor_4_3_3_scaled` and
  `phi4_single_site_nonneg` are proved in `BallBoundarySimonLieb/Tight.lean` and
  `ContinuousSpin/Phi4AllOdd.lean`, respectively.

See the [theorem catalogue](theorems/index.html),
[Chapters 2--10 coverage](coverage/chapters-2-10.html), and
[Chapter 17 coverage](coverage/chapter-17.html) for detailed statements and provenance.
