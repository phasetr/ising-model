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

/-! ## Moved: along-ex tanh ferro tail wrappers

The four trailing along-ex tanh ferro wrappers
(`vdPolymerFamilies_sumAlongExhaustion_*_tanh_{gt,eq}_one_iff_ferro`,
`polymerFreeEnergyAlongExhaustion_*_tanh_lt_{pow_sub_one,eps}_of_eps_pos_ferro`)
now live in `MayerTanhFerromagneticIffAlongExTail.lean`. -/



end Ambient
end IsingModel
