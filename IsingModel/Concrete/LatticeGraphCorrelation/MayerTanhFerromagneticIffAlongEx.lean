import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff

/-!
# Concrete AlongExhaustion Mayer tanh ferromagnetic iff wrappers

Narrow child module for nine ℤ^d
`*AlongExhaustion_latticeGraph_tanh_*_ferro` Mayer tanh ferromagnetic
iff wrappers (`polymerFreeEnergyAlongExhaustion_*` and
`vdPolymerFamilies_sumAlongExhaustion_*`). Each wrapper is a thin
pass-through to the corresponding ambient `*_AlongExhaustion_tanh_*_ferro`
lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d along-ex: pFE(tanh) < eps(tanh) iff eps(tanh) > 0** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_eps_iff_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
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
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: pFE(tanh) = 0 iff eps(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_eq_zero_iff_eps_eq_zero_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: 0 < pFE(tanh) iff 0 < eps(tanh)** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_iff_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: 0 < pFE(tanh) iff 0 < tanh and allPolymers nonempty**
(ferro). -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: pFE(tanh) = 0 iff tanh = 0 or allPolymers empty**
(ferro). -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_eq_zero_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: 1 < vdSum(tanh) iff 0 < tanh and allPolymers nonempty**
(ferro). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: vdSum(tanh) = 1 iff tanh = 0 or allPolymers empty**
(ferro). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_eq_one_iff_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n

/-- **Z^d along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under
eps(tanh) > 0 (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
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
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n h_eps_pos

/-- **Z^d along-ex: pFE(tanh) < eps(tanh)** under eps(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_eps_of_eps_pos_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
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
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos_ferro
    (IsingModel.latticeGraph d) Λ hβ hJ n h_eps_pos

end Ambient
end IsingModel
