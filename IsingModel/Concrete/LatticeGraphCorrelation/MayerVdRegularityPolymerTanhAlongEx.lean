import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityVdPolymerTanh

/-!
# ℤ^d vdPolymerFamilies_sumAlongEx tanh regularity wrappers

Narrow child module for four ℤ^d
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_*` regularity
wrappers extracted from `MayerVdRegularityPolymerTanh.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_beta`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_J`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_beta`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_J`.

Each result is a thin pass-through of the ambient
`Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerVdRegularityPolymerTanh` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ β n

end Ambient
end IsingModel
