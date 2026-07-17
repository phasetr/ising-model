import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Concrete polymer free-energy epsilon sharpening wrappers

Narrow child module for concrete `Z^d` wrappers around the ambient
`epsilon(t)` nonnegativity and non-tanh polymer free-energy sharpening API.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 epsilon(t) nonneg + non-tanh polymerFreeEnergy sharpening
Z^d wraps -/

/-- **Z^d Λ: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hn

/-! ## Moved: Λ-layer polymerFreeEnergy ε iff wrappers

The three wrappers
`polymerFreeEnergy_Λ_latticeGraph_eq_zero_iff_eps_eq_zero`,
`polymerFreeEnergy_Λ_latticeGraph_pos_iff_eps_pos`,
`polymerFreeEnergy_Λ_latticeGraph_lt_eps_iff_eps_pos` now live in
`PolymerFreeEnergyEpsilonSharpeningIff.lean`. -/


/-- **Z^d Λ: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t`, ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_latticeGraph_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t <
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ ht h_eps_pos

/-! ## Moved: AlongExhaustion polymer free-energy epsilon-sharpening wrappers

The six AlongExhaustion `vdPolymerFamilies_sumAlongExhaustion_*` /
`polymerFreeEnergyAlongExhaustion_*` epsilon-sharpening wrappers now
live in `PolymerFreeEnergyEpsilonSharpeningAlongEx.lean`. -/


end Ambient
end IsingModel
