import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity

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

/-- **ℤ^d along-ex: vdPolymerFamilies_sum Continuous in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum Differentiable ℝ in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum HasDerivAt**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (IsingModel.latticeGraph d) Λ n t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J ℤ^d wraps -/
/-! ## Moved: vdPolymerFamilies_sum tanh regularity wrappers

The eight `vdPolymerFamilies_sum_{Λ,AlongExhaustion}_latticeGraph_tanh_{continuous,differentiable}_{beta,J}`
wrappers now live in `MayerVdRegularityPolymerTanh.lean`. -/


end Ambient

end IsingModel
