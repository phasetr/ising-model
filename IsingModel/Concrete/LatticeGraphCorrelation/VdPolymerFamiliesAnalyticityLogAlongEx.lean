import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityLog

/-!
# ℤ^d analyticity of the logarithm of the polymer-family activity sum

Concrete `latticeGraph d` statements at a fixed stage of an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, about the logarithm of the sum over the compatible polymer families of the
induced subgraph. As a function of the activity it is analytic at every non-negative point,
and analytic on a neighbourhood of `Set.Ici 0` with no hypothesis at all. Composed with
`Real.tanh` of the product of inverse temperature and coupling, it is analytic in the inverse
temperature and analytic in the coupling wherever that product is non-negative. Every
statement requires a `Fintype` instance on the edge set induced at every stage.
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
