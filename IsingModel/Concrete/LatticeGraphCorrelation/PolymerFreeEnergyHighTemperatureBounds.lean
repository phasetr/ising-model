import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Concrete polymer free-energy high-temperature bound wrappers

Narrow child module for the §18.5 `vdPolymerFamilies_sum` sandwich/monotone,
`ε(t)` bound, and `polymerFreeEnergy(tanh)` high-temperature bound wrappers on
`latticeGraph d`. The theorem names are the same as the former
declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ## §18.5 polymer free-energy high-temperature bounds ℤ^d wraps -/

/-- **ℤ^d Λ: vdSum sandwich for `t ≥ 0`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_le_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-! ## Moved: Λ-direct polymerFreeEnergy_Λ tanh bound wrappers

The three Λ-direct `polymerFreeEnergy_Λ_latticeGraph_tanh_*` bound
wrappers (`_le_eps`, `_le_pow_sub_one`, `_lt_log_two_of_pow_lt_two`)
now live in `PolymerFreeEnergyHighTemperatureBoundsPFE.lean`. -/



/-! ## Moved: AlongExhaustion polymer free-energy high-temperature bounds

The six AlongExhaustion `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*` wrappers now
live in `PolymerFreeEnergyHighTemperatureBoundsAlongEx.lean`. -/



end Ambient
end IsingModel
