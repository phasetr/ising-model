import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Concrete Mayer vd iff characterization wrappers

Narrow child module for concrete `ℤ^d` iff characterizations of
`vdPolymerFamilies_sum`. This keeps callers that only need these wrappers out
of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 vdPolymerFamilies_sum iff characterizations ℤ^d wraps -/

/-- **ℤ^d Λ: vdSum = 1 ↔ ε = 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_eq_one_iff_eps_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: vdSum > 1 ↔ ε > 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_gt_one_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_eq_one_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-! ## Moved: along-ex vdPolymerFamilies_sum _iff wrappers

The four `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*_iff`
wrappers (`_eq_one_iff_eps_eq_zero`, `_gt_one_iff_eps_pos`,
`_tanh_gt_one_iff`, `_tanh_eq_one_iff`) now live in
`MayerVdIffAlongEx.lean`. -/



end Ambient
end IsingModel
