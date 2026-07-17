import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer
import IsingModel.Lattice

/-!
# Concrete vdPolymerFamilies_sum tanh regularity wrappers

Narrow child module for eight ℤ^d
`vdPolymerFamilies_sum_{Λ,AlongExhaustion}_latticeGraph_tanh_{continuous,differentiable}_{beta,J}`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `vdPolymerFamilies_sum_*_tanh_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ β

/-! ## Moved: AlongEx vdPolymerFamilies tanh regularity wrappers

The four wrappers
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_beta`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_continuous_J`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_beta`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_differentiable_J` now
live in `MayerVdRegularityPolymerTanhAlongEx.lean`. -/


end Ambient
end IsingModel
