import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity

/-!
# Concrete polymer-family analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `vdPolymerFamilies_sum`,
`log_vdPolymerFamilies_sum`, and epsilon analyticity wrappers. The theorem names
are the same as the former declarations, but callers can now import this
child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### `vdPolymerFamilies_sum` analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: vdPolymerFamilies_sum AnalyticAt ℝ in t**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sum_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d along-ex: vdPolymerFamilies_sum AnalyticAt ℝ in t**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ n t

/-! ## Moved: vdPolymerFamilies_sum tanh analyticity wrappers

The four wrappers
`vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_beta`,
`vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_J`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J` now
live in `VdPolymerFamiliesAnalyticityTanh.lean`. -/


/-! ### `log_vdPolymerFamilies_sum` analyticity ℤ^d wraps -/
/-! ## Moved: log_vdPolymerFamilies_sum analyticity wrappers

The four remaining
`log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` analyticity
wrappers now live in `VdPolymerFamiliesAnalyticityLogAlongEx.lean`. The
four Λ-direct `log_vdPolymerFamilies_sum_Λ_latticeGraph_*` counterparts
were deleted; no consumer of them was found in this repository. -/

/-! ### Epsilon analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_analyticAt
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d along-ex: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_analyticAt
    (IsingModel.latticeGraph d) Λ t n

end Ambient
end IsingModel
