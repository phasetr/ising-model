import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff

/-!
# Concrete Mayer tanh ferromagnetic iff wrappers

Narrow child module for concrete `Z^d` ferromagnetic tanh iff wrappers for
`polymerFreeEnergy` and `vdPolymerFamilies_sum`. This keeps callers that only
need these forwarders out of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
Z^d wraps -/

/-- **Z^d Λ: pFE(tanh) < eps(tanh) iff eps(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_iff_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: pFE(tanh) = 0 iff eps(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff_eps_eq_zero_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: 0 < pFE(tanh) iff 0 < eps(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff_eps_pos_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: 0 < pFE(tanh) iff 0 < tanh and allPolymers nonempty** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-- **Z^d Λ: pFE(tanh) = 0 iff tanh = 0 or allPolymers empty** (ferro). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ

/-! ## Moved: Λ-layer vdSum iff and pFE-comparison-under-eps-pos wrappers

The four wrappers
`vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_iff_ferro`,
`vdPolymerFamilies_sum_Λ_latticeGraph_tanh_eq_one_iff_ferro`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos_ferro`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_of_eps_pos_ferro` now
live in `MayerTanhFerromagneticIffVdSum.lean`. -/


/-! ## Moved: AlongExhaustion Mayer tanh ferromagnetic iff wrappers

The four `*AlongExhaustion_latticeGraph_tanh_*_ferro` tail wrappers
live in `MayerTanhFerromagneticIffAlongExTail.lean`. -/


end Ambient
end IsingModel
