import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer
import IsingModel.Lattice

/-!
# Concrete vdPolymerFamilies regularity wrappers

Narrow child module for the 12 ℤ^d
`vdPolymerFamilies_sum_Λ_latticeGraph_*` and
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` wrappers
(Continuous/Differentiable/HasDerivAt in t, plus tanh-variants in
β/J) extracted from `MayerVdRegularity.lean` in PR #2045. Each is a
thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum*` regularity lemma at `IsingModel.latticeGraph d`.
The theorem names are unchanged from the former `MayerVdRegularity`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.6 vdPolymerFamilies_sum regularity in t ℤ^d wraps -/

/-- **ℤ^d Λ: vdPolymerFamilies_sum Continuous in t**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_continuous (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: vdPolymerFamilies_sum Differentiable ℝ in t**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_differentiable
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_differentiable
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: vdPolymerFamilies_sum HasDerivAt**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  Ambient.vdPolymerFamilies_sum_Λ_hasDerivAt
    (IsingModel.latticeGraph d) Λ t

/-! ## Moved: AlongEx vdPolymerFamilies_sum t-regularity wrappers

The three wrappers
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_continuous`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_differentiable`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_hasDerivAt` now live
in `MayerVdRegularityPolymerAlongEx.lean`. -/


/-! ### §18.5 vdPolymerFamilies_sum tanh β/J ℤ^d wraps -/
/-! ## Moved: vdPolymerFamilies_sum tanh regularity wrappers

The eight wrappers
`vdPolymerFamilies_sum_{Λ,AlongExhaustion}_latticeGraph_tanh_*`
(`continuous_beta`, `continuous_J`, `differentiable_beta`,
`differentiable_J` in each direction) now live in
`MayerVdRegularityPolymerTanh.lean`. -/


end Ambient

end IsingModel
