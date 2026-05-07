import IsingModel.AmbientLattice.CorrelationDecay
import IsingModel.Lattice

/-!
# Lightweight concrete lattice correlation-decay wrappers

This module exposes concrete `latticeGraph d` high-temperature
correlation-decay wrappers without importing the monolithic
`LatticeGraphCorrelation.lean` file. It keeps incremental checks for
thin correlation-decay API additions away from the heavy ambient
analyticity and cluster-expansion import chain.
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

end Ambient
end IsingModel
