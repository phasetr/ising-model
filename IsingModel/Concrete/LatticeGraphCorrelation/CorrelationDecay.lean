import IsingModel.AmbientLattice.CorrelationDecay
import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.Lattice
import IsingModel.Inequalities.HighTemp.SummabilityCluster

/-!
# Lightweight concrete lattice correlation-decay wrappers

This module exposes concrete `latticeGraph d` cluster-decay and
high-temperature correlation-decay wrappers without importing the original
monolithic special-cases module. It keeps
incremental checks for thin correlation-decay API additions away from the
heavy ambient analyticity and cluster-expansion import chain.
-/

namespace IsingModel
namespace Ambient

/-- The finite induced subgraph of `latticeGraph d` on any finite volume
has a finite edge set. This local instance keeps the lightweight concrete
correlation-decay wrappers independent of heavier concrete modules. -/
noncomputable local instance fintype_induced_latticeGraph_edgeSet
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
  classical
  exact SimpleGraph.fintypeEdgeSet _

/-! ## ℤ^d wrapper for §5.1 conditional cluster decay (PR #779) -/

/-- **ℤ^d conditional cluster decay (cofinite form)**: on ℤ^d, if the
∞-volume Ursell 2-point function at a fixed site `i : Fin d → ℤ`,
viewed as a function of the free site `j : Fin d → ℤ`, is summable,
then it tends to `0` along `Filter.cofinite` (which on `Fin d → ℤ`
coincides with the "|r| → ∞" filter). Concrete `latticeGraph d`
wrapper for PR #779's
`truncated2Infinite_tendsto_cofinite_zero_of_summable`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      Filter.cofinite (nhds 0) :=
  truncated2Infinite_tendsto_cofinite_zero_of_summable
    (IsingModel.latticeGraph d) Λ p i hsum

/-! ## ℤ^d distance-based cluster decay capstone

Combines PR #779's cofinite cluster decay with PR #782's proper-map
property of `latticeDistance` (via the filter equality
`comap_latticeDistance_atTop_eq_cofinite` from PR #783) to express
the §5.1 cluster decay statement in its standard distance-based
form. -/

/-- **ℤ^d distance-based conditional cluster decay**: under
summability of `j ↦ U_2(i, j)` at a fixed basepoint
`i : Fin d → ℤ`, the ∞-volume Ursell 2-point function tends to `0`
as the lattice distance `latticeDistance d i j` tends to infinity.

Equivalent ε-N statement: for every `ε > 0` there exists `N : ℕ`
such that `latticeDistance d i j ≥ N` implies
`|truncated2Infinite (latticeGraph d) Λ p i j| < ε`.

A `Summable`-conditioned corollary, not a standalone Glimm–Jaffe
result: it presents the §5.1 cluster picture in its distance-based
form, with the `Summable` hypothesis serving as a placeholder for
the unconditional summability later supplied in high-temperature regimes by
the Simon–Lieb stack (Friedli–Velenik Prop 9.31). This PR #783-era capstone
of the §5.1 cluster-decay infrastructure stack (PR #779 + PR #781 + PR #782)
remains the conditional distance-form wrapper. The proof is a one-line rewrite
of the comap filter via `comap_latticeDistance_atTop_eq_cofinite`, followed by
PR #779's cofinite version.

References: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1
pp. 76–79; Friedli–Velenik *Statistical Mechanics of Lattice
Systems*, Prop 9.31 (Simon–Lieb inequality). -/
theorem truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      (Filter.comap (fun j : Fin d → ℤ =>
        IsingModel.latticeDistance d i j) Filter.atTop) (nhds 0) := by
  rw [IsingModel.comap_latticeDistance_atTop_eq_cofinite]
  exact truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    d Λ p i hsum

/-! ## ℤ^d wrappers for §5.1 cluster property (PR #792 bundle) -/

/-! ## Moved: clusterProperty_latticeGraph wrappers

The three wrappers
`clusterProperty_latticeGraph_of_summable`,
`clusterProperty_latticeGraph_J_zero`,
`clusterProperty_latticeGraph_beta_zero` now live in
`CorrelationDecayClusterProperty.lean`. -/


/-- **ℤ^d Λ ferromagnetic §18.7 named-rate capstone**: under
`0 ≤ J, 0 < β`, the finite-volume pair-correlation distance bound on
`latticeGraph d` is written with `highTempExpRate`. -/
theorem
correlationΛ_latticeGraph_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j

/-- **ℤ^d along-ex ferromagnetic §18.7 named-rate capstone at stage
`n`**: under `0 ≤ J, 0 < β`, the finite-volume pair-correlation distance
bound on `latticeGraph d` is written with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_highTempExpRate_dist_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_highTempExpRate_dist_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n i j

/-- **ℤ^d Λ ferromagnetic §18.7 named monotone-rate capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ highTempExpRate β J` gives the finite-volume
pair-correlation distance bound on `latticeGraph d` with rate `α`. -/
theorem correlationΛ_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β α : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β α hJ hβ hα i j

/-- **ℤ^d along-ex ferromagnetic §18.7 named monotone-rate capstone at
stage `n`**: under `0 ≤ J, 0 < β`, any
`α ≤ highTempExpRate β J` gives the finite-volume pair-correlation
distance bound on `latticeGraph d` with rate `α`. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.exp (-α *
          ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferro
    (IsingModel.latticeGraph d) Λ J β α hJ hβ hα n i j

/-! ## ℤ^d UNCONDITIONAL high-temperature distance cluster decay (Issue #4274, GJ §5.1)

Discharges the `Summable` hypothesis of the wrappers above at high temperature, giving the
unconditional ℤ^d cluster-decay statement.  The summability discharge is
`truncated2Infinite_summable_of_high_temp` (finite susceptibility bound `βJ·2d/(1−βJ·2d)`, FV §3.7.3
/ Simon–Lieb GKS-II); the per-vertex degree bound `≤ 2d` is `edgeFilter_card_eq_degree` +
`inducedLatticeGraph_degree_le`, exactly as in `clusterProperty_latticeGraph_of_high_temp`.
Axiom-free: the chain is the GKS/Simon–Lieb finite-volume correlation-inequality layer only. -/

/-- **ℤ^d high-temperature summability of the Ursell two-point function** (GJ §5.1; FV §3.7.3): for
the `d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and `β·J·2d < 1`,
the infinite-volume Ursell two-point function `j ↦ U₂(i, j)` is summable.  The induced cubic-lattice
graph has per-vertex incident-edge count `≤ 2d`, so `truncated2Infinite_summable_of_high_temp`
applies with `D = 2d`. -/
theorem truncated2Infinite_latticeGraph_summable_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  classical
  refine truncated2Infinite_summable_of_high_temp
    (IsingModel.latticeGraph d) Λ hf (D := 2 * d) ?_ hlt i
  intro n v
  rw [edgeFilter_card_eq_degree v]
  exact inducedLatticeGraph_degree_le d _ v

/-- **ℤ^d unconditional high-temperature distance cluster decay** (GJ §5.1).

Unconditional version of `truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable`: for the
`d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and the Simon–Lieb
high-temperature condition `β·J·2d < 1`, the infinite-volume Ursell two-point function `U₂(i, j)`
tends to `0` as `latticeDistance d i j → ∞`.  The `Summable` hypothesis is discharged by
`truncated2Infinite_latticeGraph_summable_of_high_temp`. -/
theorem truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j)
      (Filter.comap (fun j : Fin d → ℤ => IsingModel.latticeDistance d i j) Filter.atTop)
      (nhds 0) :=
  truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) i
    (truncated2Infinite_latticeGraph_summable_of_high_temp d Λ hf hlt i)

/-- **ℤ^d unconditional high-temperature distance cluster decay (cofinite form)** (GJ §5.1): the
`Filter.cofinite` companion of `truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_high_temp`. -/
theorem truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_high_temp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β J : ℝ}
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) (hlt : β * J * ↑(2 * d) < 1) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j)
      Filter.cofinite (nhds 0) :=
  truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) i
    (truncated2Infinite_latticeGraph_summable_of_high_temp d Λ hf hlt i)

end Ambient
end IsingModel
