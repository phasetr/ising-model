import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplexAlongEx

/-!
# ℤ^d per-stage complex partition-function bounds

Part of the split per-stage complex bounds layer for the GJ §4.6 Vitali route.
-/

namespace IsingModel
namespace Ambient

/-! #### Per-stage continuity, norm, logarithmic, and Lee-Yang nonvanishing wrappers -/

/-- **ℤ^d per-stage `Continuous` in `h`** for
`partitionFunctionComplexAlongExhaustion`. -/
theorem partitionFunctionComplexAlongExhaustion_continuous_h_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) :
    Continuous
      (fun h => Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n) :=
  Ambient.partitionFunctionComplexAlongExhaustion_continuous_h_stage
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d per-stage locally-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: `‖Z_ℂ_{Λ_n}‖ ≤ 2^|Λ_n| · exp(...)`
under `|Re h| ≤ R`. Montel input for the Vitali extraction. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) {R : ℝ} {h : ℂ} (hh : |h.re| ≤ R) :
    ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
      ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
          Real.exp (|β| *
            (|J| * (Ambient.inducedGraph
                (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
              + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.norm_partitionFunctionComplexAlongExhaustion_le_of_re_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hh

/-- **ℤ^d per-stage compact-uniform norm bound** for
`partitionFunctionComplexAlongExhaustion`: on any compact field set `K`, a
single real-part bound `R` feeds all stage-wise `Z_ℂ` norm estimates. The
bound remains stage-dependent and is an envelope for later normalised estimates. -/
theorem norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n, ∀ h ∈ K,
      ‖Ambient.partitionFunctionComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        ≤ Fintype.card (IsingModel.Config (↑(Λ.volume n) : Type _)) *
            Real.exp (|β| *
              (|J| * (Ambient.inducedGraph
                  (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
                + R * Fintype.card (↑(Λ.volume n) : Type _))) :=
  Ambient.norm_partitionFunctionComplexAlongExhaustion_le_on_isCompact_stage
    (IsingModel.latticeGraph d) Λ β J hK

/-- **ℤ^d per-stage upper bound on normalised `Real.log ‖Z_ℂ‖`**:
under `|Re h| ≤ R` and nonvanishing, the complex partition-function envelope
gives the corresponding upper bound for
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (β J : ℝ) (n : ℕ) [Nonempty (↑(Λ.volume n) : Type _)] {R : ℝ} {h : ℂ}
    (hZ : Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0)
    (hh : |h.re| ≤ R) :
    Real.log ‖Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)
      ≤ Real.log 2 +
        |β| * (|J| * (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
          + R * Fintype.card (↑(Λ.volume n) : Type _))
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  Ambient.real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_re_bound_stage
    (IsingModel.latticeGraph d) Λ β J n hZ hh

/-- **ℤ^d per-stage `Z_ℂ ≠ 0 on leeYangDomain`** for
`partitionFunctionComplexAlongExhaustion` (ferromagnetic). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (J : ℂ) h (β : ℂ) n ≠ 0 :=
  Ambient.partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
    (IsingModel.latticeGraph d) Λ hβ hJ n hh

end Ambient
end IsingModel
