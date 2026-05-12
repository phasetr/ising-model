import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening

/-!
# Concrete AlongExhaustion polymerFreeEnergy tanh sharpening wrappers

Narrow child module for nine ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*` sharpening + β/J
strict-mono wrappers. Each wrapper is a thin pass-through to the
corresponding ambient `polymerFreeEnergyAlongExhaustion_tanh_*` lemma
at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_eps_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_eq_zero_iff_eps_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_eps_of_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ n h_eps_pos

/-- **ℤ^d along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under
ε(tanh) > 0. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ hβJ n h_eps_pos

/-- **ℤ^d along-ex: strict pFE(tanh) in β under polymers ≠ ∅**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_beta_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β₂ * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hβ₁ hJ hβ

/-- **ℤ^d along-ex: strict pFE(tanh) in J under polymers ≠ ∅**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_J_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J₂)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hJ₁ hβ hJ

/-- **ℤ^d along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in
β**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_beta_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hJ

/-- **ℤ^d along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in
J**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_J_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hβ

end Ambient
end IsingModel
