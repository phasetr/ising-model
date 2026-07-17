import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# Concrete Mayer epsilon positivity wrappers

Narrow child module for concrete `ℤ^d` `ε(t)` and `polymerFreeEnergy`
positivity/zero iff wrappers. This keeps callers that only need these
forwarders out of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff ℤ^d wraps -/

/-- **ℤ^d Λ: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pos_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_eq_zero_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tanh_pos_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_tanh_eq_zero_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-! ## Moved: polymerFreeEnergy_Λ_tanh _iff wrappers

The two Λ-direct `polymerFreeEnergy_Λ_latticeGraph_tanh_{pos,eq_zero}_iff`
wrappers now live in `MayerEpsilonPositivityPFE.lean`. -/



/-! ## Moved: AlongExhaustion mayer-epsilon positivity / equality wrappers

The six AlongExhaustion `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*` positivity /
equality wrappers now live in `MayerEpsilonPositivityAlongEx.lean`. -/



end Ambient
end IsingModel
