import IsingModel.AmbientComplexAnalyticity.Basic.UpperBounds

/-!
# Lower polynomial-bound wrappers

This module contains wrappers split from `AmbientComplexAnalyticity.Basic`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Stage lower normalised-log bridge from a Lee-Yang polynomial lower
witness**: if the Lee-Yang polynomial factor at stage `n` has a positive lower
witness `ε` and `|Re h| ≤ R`, then the finite-volume `Z_ℂ` lower bound gives
the corresponding lower bound for
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|`.

This theorem is still stagewise: the witness `ε` may depend on `n` and `h`. -/
theorem real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_ge_of_poly_lower_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R ε : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) {h : ℂ}
    (hR : |h.re| ≤ R) (hε : 0 < ε)
    (hpoly :
      ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖) :
    Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) - β * R
      ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hZlower :
      Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε
        ≤ ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ := by
    simpa [partitionFunctionComplexAlongExhaustion] using
      IsingModel.norm_partitionFunctionComplex_ge_exp_mul_isingEdgePoly_lower
        (inducedGraph G (Λ.volume n)) hβ hJ hR hε.le hpoly
  have hprod_pos :
      0 < Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε :=
    mul_pos (Real.exp_pos _) hε
  have hZ_pos :
      0 < ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    hprod_pos.trans_le hZlower
  have hlog_le :
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ :=
    (Real.log_le_log_iff hprod_pos hZ_pos).mpr hZlower
  have hlog_prod :
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        =
      -β * R * Fintype.card (↑(Λ.volume n) : Type _) + Real.log ε := by
    rw [Real.log_mul (Real.exp_pos _).ne' hε.ne', Real.log_exp]
  calc
    Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) - β * R
        =
      Real.log (Real.exp (-β * R * Fintype.card (↑(Λ.volume n) : Type _)) * ε)
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
          rw [hlog_prod]
          field_simp [hcard_pos.ne']
          ring
    _ ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
          div_le_div_of_nonneg_right hlog_le hcard_pos.le

/-- **Lower normalised-log handoff from polynomial-factor witnesses**:
if every stage and field in `K` has a positive polynomial-factor lower witness
`ε`, and the normalised logarithms of these witnesses are uniformly bounded
below, then the complex partition functions satisfy the lower normalised-log
hypothesis consumed by the Lee-Yang locally bounded family handoff.

This isolates the remaining hard input on the polynomial witnesses; it does not
prove a stage-uniform lower bound for them. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) {K : Set ℂ}
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  rcases hPolyLower with ⟨Lε, hLε⟩
  refine ⟨Lε + β * R, ?_⟩
  intro n h hh
  rcases hLε n h hh with ⟨ε, hε_pos, hpoly, hlogε⟩
  have hstage :=
    real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_ge_of_poly_lower_stage
      G Λ hβ hJ n (hR h hh) hε_pos hpoly
  linarith

/-- **Compact Lee-Yang polynomial lower witnesses**: compact containment in
`leeYangDomain` gives a stage-uniform lower normalised-log bound for the
positive Lee-Yang polynomial witnesses. The witness is
`ε_n = (1-r)^{|Λ_n|}`, where `r < 1` is the compact fugacity gap. -/
theorem exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
  rcases IsingModel.exists_leeYangFugacity_norm_le_lt_one_on_isCompact hβ hK hKsub
    with ⟨r, hr_lt, hrbound⟩
  let s : ℝ := max r 0
  have hs0 : 0 ≤ s := le_max_right r 0
  have hs1 : s < 1 := max_lt hr_lt zero_lt_one
  have hspos : 0 < 1 - s := by linarith
  refine ⟨-Real.log (1 - s), ?_⟩
  intro n h hh
  let ε : ℝ := (1 - s) ^ Fintype.card (↑(Λ.volume n) : Type _)
  have hε_pos : 0 < ε := by
    exact pow_pos hspos _
  have ht₀ : 0 ≤ Real.exp (-2 * β * J) := (Real.exp_pos _).le
  have ht₁ : Real.exp (-2 * β * J) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < 2 * β * J := by positivity
    linarith
  have hz : ‖IsingModel.leeYangFugacity (β : ℂ) h‖ ≤ s :=
    (hrbound h hh).trans (le_max_left r 0)
  have hpoly :
      ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ := by
    simpa [ε] using
      IsingModel.one_sub_radius_pow_card_le_norm_isingEdgePoly_eval_leeYangFugacityVec
        (G := inducedGraph G (Λ.volume n)) ht₀ ht₁ hs0 hs1 hz
  have hcard_pos : (0 : ℝ) < (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (↑(Λ.volume n) : Type _))
  have hlogε :
      Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) =
        Real.log (1 - s) := by
    unfold ε
    rw [Real.log_pow]
    field_simp [hcard_pos.ne']
  exact ⟨ε, hε_pos, hpoly, by rw [hlogε]; simp⟩

/-- **Compact Lee-Yang lower normalised-log bound**: the quantitative
root-product lower bound for the Lee-Yang polynomial supplies the lower-log
hypothesis for the complex partition functions on any compact
`K ⊆ leeYangDomain`. -/
theorem exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R) :
    ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
  exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
    G Λ hβ.le hJ.le hR
    (exists_poly_lower_norm_isingEdgePoly_eval_leeYangFugacityVec_on_isCompact
      G Λ hβ hJ hK hKsub)

end Ambient

end IsingModel
