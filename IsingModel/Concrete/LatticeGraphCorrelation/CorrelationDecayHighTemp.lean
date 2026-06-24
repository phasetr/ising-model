import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Inequalities.HighTemp.SummabilityCluster

/-!
# Unconditional high-temperature distance cluster decay on ℤ^d (GJ §5.1, Issue #4274)

`CorrelationDecay.lean` proves the ℤ^d cluster-decay statement only *conditionally* on a `Summable`
hypothesis (`truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable`), flagged there as "a
placeholder for the unconditional summability later supplied by the Simon–Lieb stack".  This file
discharges that hypothesis at high temperature, giving the **unconditional** statement: for the
`d`-dimensional lattice with any exhaustion, ferromagnetic `⟨J, 0, β⟩`, and the Simon–Lieb
high-temperature condition `β·J·2d < 1`, the infinite-volume Ursell (truncated) two-point function
`U₂(i, j)` tends to `0` as the ℓ¹-lattice distance `latticeDistance d i j → ∞`.

The `Summable` discharge is `truncated2Infinite_summable_of_high_temp`
(`Inequalities/HighTemp/SummabilityCluster.lean`), which controls the partial sums by the finite
susceptibility bound `βJ·2d/(1 − βJ·2d)` (FV §3.7.3 / Simon–Lieb GKS-II); the per-vertex degree
bound `≤ 2d` comes from `edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`, exactly as in
`clusterProperty_latticeGraph_of_high_temp`.  Axiom-free: the whole chain is the GKS/Simon–Lieb
finite-volume correlation-inequality layer and never touches the Vitali axiom or the cluster-expansion
analyticity stack.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §5.1, pp. 72–79;
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3 (Simon–Lieb /
susceptibility bound).
-/

namespace IsingModel

open Ambient

noncomputable local instance fintype_induced_latticeGraph_edgeSet'
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
  classical
  exact SimpleGraph.fintypeEdgeSet _

/-- **ℤ^d high-temperature summability of the Ursell two-point function** (GJ §5.1; FV §3.7.3).

For the `d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and the
Simon–Lieb high-temperature condition `β·J·2d < 1`, the infinite-volume Ursell two-point function
`j ↦ U₂(i, j)` is summable.  The per-vertex incident-edge count of the induced cubic-lattice graph is
at most `2d` (`edgeFilter_card_eq_degree` + `inducedLatticeGraph_degree_le`), so
`truncated2Infinite_summable_of_high_temp` applies with `D = 2d`. -/
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
`d`-dimensional lattice with any exhaustion `Λ`, ferromagnetic `⟨J, 0, β⟩`, and `β·J·2d < 1`, the
infinite-volume Ursell two-point function `U₂(i, j)` tends to `0` as `latticeDistance d i j → ∞`.
The `Summable` hypothesis is discharged by `truncated2Infinite_latticeGraph_summable_of_high_temp`. -/
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

/-- **ℤ^d unconditional high-temperature distance cluster decay (cofinite form)** (GJ §5.1).

The `Filter.cofinite` companion of `truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_high_temp`
(on `Fin d → ℤ`, `cofinite` coincides with the "`|r| → ∞`" filter). -/
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

end IsingModel
