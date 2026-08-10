import IsingModel.AmbientLattice.Defs.HighTempPartition.Ratios

/-!
# Λ-restricted high-temperature slice comparison, bundled across the three quantities

Conjunctions that gather the comparison of `partitionFunctionΛ`, of its logarithm and of
`freeEnergyΛ` at `⟨J, 0, β⟩` against one degenerate slice into a single statement, for an
arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`. The two such
conjunctions differ only in which slice they use, `⟨0, 0, β⟩` or `⟨J, 0, 0⟩`; the external
field is zero in every record occurring here. The bounds are written with the number of
edges of `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces.

Inside a conjunction, under `0 ≤ β * J`, the partition function at `⟨J, 0, β⟩` divided by
the partition function at the slice lies between `cosh (β * J)` raised to the edge count and
`exp (β * J * edge count)`; the difference of the logarithms lies between the edge count
times `log (cosh (β * J))` and `β * J` times the edge count; and the difference of the free
energies lies between the edge count over `Λ.card` times `log (cosh (β * J))` and `β * J`
times the edge count over `Λ.card`. The partition function is therefore the only one of the
three that is compared multiplicatively.

Beside the conjunctions stand the upper halves of the free-energy comparison, one for each
slice, assuming `0 ≤ J` together with `0 < β` rather than `0 ≤ β * J`. Every statement here
assumes `0 < Λ.card` and takes `[DecidableEq V]` together with
`[Fintype (inducedGraph G Λ).edgeSet]`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level triple (Z + log Z + f) ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).1,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).1⟩

/-- **Λ-level triple ratio sandwich bundle at β=0**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
        ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card)) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card) ∧
    (((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
        Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card) :=
  ⟨partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G Λ J β hβJ,
   (log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
     G Λ J β hβJ).2,
   (freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle G Λ J β hβJ hne).2⟩

/-- **Λ-level ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    G Λ J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
