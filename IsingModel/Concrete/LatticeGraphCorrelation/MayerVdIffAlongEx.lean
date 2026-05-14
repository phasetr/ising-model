import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdIff

/-!
# Concrete along-exhaustion §18.5 Mayer VdIff wrappers

Narrow child module for 4 ℤ^d along-exhaustion
`vdPolymerFamilies_sumAlongExhaustion_*_iff` wrappers extracted from
`MayerVdIff.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_eq_one_iff_eps_eq_zero`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_gt_one_iff_eps_pos`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_iff`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_eq_one_iff`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.vdPolymerFamilies_sumAlongExhaustion_*_iff_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerVdIff` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: vdSum = 1 ↔ ε = 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_eq_one_iff_eps_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_eq_one_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: vdSum > 1 ↔ ε > 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_gt_one_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_gt_one_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n))).Nonempty :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_eq_one_iff
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) = ∅ :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff
    (IsingModel.latticeGraph d) Λ hβJ n

end Ambient
end IsingModel
