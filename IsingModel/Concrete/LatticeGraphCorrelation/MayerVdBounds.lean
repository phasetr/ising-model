import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Concrete Mayer vd bound wrappers

Narrow child module for concrete `ℤ^d` `vdPolymerFamilies_sum` bound
wrappers. This keeps callers that only need these forwarders out of the
monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 vdPolymerFamilies_sum bound family ℤ^d wraps -/

/-- **ℤ^d Λ: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_two_pow
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_two_pow
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_one_plus_tanh_pow
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  Ambient.one_le_vdPolymerFamilies_sum_Λ
    (IsingModel.latticeGraph d) Λ hβJ
/-! ## Moved: along-ex vdPolymerFamilies_sumAlongExhaustion bound wrappers

The three along-ex `vdPolymerFamilies_sumAlongExhaustion_*` tanh-bound
wrappers (`_le_two_pow`, `_le_one_plus_tanh_pow`, `one_le_*`) now live
in `MayerVdBoundsAlongEx.lean`. -/



/-! ## Moved: generic-t Λ vdPolymerFamilies_sum bound wrappers

The four Λ `vdPolymerFamilies_sum_Λ_latticeGraph_*` generic-`t` bound
wrappers (`ge_one_of_nonneg`, `le_one_plus_pow_of_nonneg`,
`pos_of_nonneg`, `eq_one_add`) now live in `MayerVdBoundsGenericT.lean`. -/



/-! ## Deleted: AlongEx vdPolymerFamilies_sum generic-`t` bound family

The four ℤ^d along-exhaustion generic-`t` bound wrappers of the
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` family (the lower
bound, the `(1 + t)^|E|` upper bound, positivity under `0 ≤ t`, and the
`1 + ε(t)` decomposition) were deleted; no consumer of them was found in
this repository. -/


end Ambient
end IsingModel
