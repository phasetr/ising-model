import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity

/-!
# ℤ^d AlongExhaustion mayer-epsilon positivity / equality wrappers

Narrow child module for four ℤ^d AlongExhaustion mayer-epsilon
positivity / equality wrappers extracted from
`MayerEpsilonPositivity.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pos_iff`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_eq_zero_iff`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_pos_iff`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_eq_zero_iff`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pos_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_iff
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_eq_zero_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_eq_zero_iff
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_pos_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_eq_zero_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_eq_zero_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-! ## Moved: polymerFreeEnergyAlongExhaustion_tanh _iff wrappers

The two along-ex `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_{pos,eq_zero}_iff`
wrappers now live in `MayerEpsilonPositivityAlongExPFE.lean`. -/


end Ambient
end IsingModel
