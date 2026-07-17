import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLog

/-!
# Concrete log_vdPolymerFamilies_sumAlongExhaustion analyticity wrappers

Narrow child module for 4 ℤ^d along-exhaustion
`log_vdPolymerFamilies_sumAlongExhaustion_*` analyticity wrappers
extracted from `VdPolymerFamiliesAnalyticityLog.lean`:

* `log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticAt`,
* `log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticOnNhd_Ici_zero`,
* `log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
* `log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.log_vdPolymerFamilies_sumAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `VdPolymerFamiliesAnalyticityLog` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: log_vdPolymerFamilies_sum AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)) t :=
  Ambient.log_vdPolymerFamilies_sumAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: log_vdPolymerFamilies_sum AnalyticOnNhd over `[0, ∞)`**. -/
theorem
log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  Ambient.log_vdPolymerFamilies_sumAlongExhaustion_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β
under `0 ≤ β·J`**. -/
theorem
log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  Ambient.log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J
under `0 ≤ β·J`**. -/
theorem
log_vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  Ambient.log_vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ n


end Ambient
end IsingModel
