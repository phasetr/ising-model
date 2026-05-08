import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity

/-!
# Concrete polymer-family analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `vdPolymerFamilies_sum`,
`log_vdPolymerFamilies_sum`, and epsilon analyticity wrappers. The theorem names
are the same as the former legacy declarations, but callers can now import this
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

/-! ### `vdPolymerFamilies_sum` tanh β/J analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J n

/-! ### `log_vdPolymerFamilies_sum` analyticity ℤ^d wraps -/

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
