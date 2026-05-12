import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening

/-!
# Concrete polymer free-energy tanh sharpening + β/J strict-mono
wrappers

Narrow child module for concrete `ℤ^d` polymer free-energy
`tanh sharpening + β/J strict-mono` wrappers. This keeps callers that
only need these forwarders out of the monolithic lattice-correlation
legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
ℤ^d wraps -/

/-- **ℤ^d Λ: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_eq_zero_iff_eps_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  Ambient.polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_pos_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_eps_of_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ h_eps_pos

/-- **ℤ^d Λ: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ h_eps_pos

/-- **ℤ^d Λ: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β₂ * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hβ₁ hJ hβ

/-- **ℤ^d Λ: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J₂)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hJ₁ hβ hJ

/-- **ℤ^d Λ: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_beta_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hJ

/-- **ℤ^d Λ: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_J_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hβ

/-! ## Moved: AlongExhaustion polymerFreeEnergy tanh sharpening wrappers

The nine `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*`
wrappers now live in `PolymerFreeEnergyTanhSharpeningAlongEx.lean`. -/


end Ambient
end IsingModel
