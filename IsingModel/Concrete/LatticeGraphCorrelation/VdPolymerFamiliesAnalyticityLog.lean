import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaVdPolymer

/-!
# Concrete log_vdPolymerFamilies_sum analyticity wrappers

Narrow child module for eight ℤ^d
`log_vdPolymerFamilies_sum_{Λ,AlongExhaustion}_latticeGraph_*` analyticity
wrappers (`analyticAt`, `analyticOnNhd_Ici_zero`, tanh substitutions in
β/J). Each wrapper is a thin pass-through to the corresponding ambient
lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: log_vdPolymerFamilies_sum AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sum_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, s ^ P.card)) t :=
  Ambient.log_vdPolymerFamilies_sum_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: log_vdPolymerFamilies_sum AnalyticOnNhd over `[0, ∞)`**. -/
theorem log_vdPolymerFamilies_sum_Λ_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  Ambient.log_vdPolymerFamilies_sum_Λ_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  Ambient.log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  Ambient.log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ

/-! ## Moved: along-ex log_vdPolymerFamilies_sum analyticity wrappers

The four along-ex `log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*`
analyticity wrappers (`analyticAt`, `analyticOnNhd_Ici_zero`,
`tanh_analyticAt_beta`, `tanh_analyticAt_J`) now live in
`VdPolymerFamiliesAnalyticityLogAlongEx.lean`. -/




end Ambient
end IsingModel
