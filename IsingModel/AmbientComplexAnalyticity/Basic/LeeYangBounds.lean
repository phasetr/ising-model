import IsingModel.AmbientComplexAnalyticity.Basic.LowerBounds

/-!
# Lee-Yang local boundedness wrappers

This module contains wrappers split from `AmbientComplexAnalyticity.Basic`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Per-stage `Z_ℂ ≠ 0 on leeYangDomain`** for
`partitionFunctionComplexAlongExhaustion` (ferromagnetic). -/
theorem partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) (n : ℕ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain
    (inducedGraph G (Λ.volume n)) hβ hJ hh

/-- **Compact-field upper normalised-log bound on Lee-Yang compact sets**:
on compact subsets of `leeYangDomain`, the Lee-Yang nonvanishing theorem
discharges the nonzero hypothesis in
`exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact`.
Thus, under bounded edge density and nonempty stages,
`Real.log ‖Z_{Λ_n}(h)‖ / |Λ_n|` has one stage-independent upper bound on
`K ⊆ leeYangDomain`. This is still only the upper half of the absolute
normalised-log input. -/
theorem exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C :=
  exists_real_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_on_isCompact
    G Λ hBED β J hK (by
      intro n h hh
      exact partitionFunctionComplexAlongExhaustion_ne_zero_on_leeYangDomain_stage
        G Λ hβ hJ n (hKsub hh))

/-- **Lee-Yang compact absolute normalised-log handoff from lower control**:
on compact `K ⊆ leeYangDomain`, the automatic Lee-Yang upper bound and a
remaining lower normalised-log hypothesis combine into the absolute
normalised-log hypothesis consumed by the free-energy bounds. -/
theorem exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      |Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖|
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) ≤ C := by
  rcases hLower with ⟨L, hL⟩
  rcases exists_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_leeYangDomain
      G Λ hBED hβ hJ hK hKsub with ⟨U, hU⟩
  refine ⟨max L U, ?_⟩
  exact abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_of_two_sided_on_set
    G Λ β J
    (by
      intro n h hh
      exact (neg_le_neg (le_max_left L U)).trans (hL n h hh))
    (by
      intro n h hh
      exact (hU n h hh).trans (le_max_right L U))

/-- **Lee-Yang compact locally bounded free-energy family from lower control**:
on compact `K ⊆ leeYangDomain`, once a stage-uniform lower normalised-log
bound is available, the Lee-Yang compact upper bound supplies the absolute-log
control and hence a stage-independent free-energy bound `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hLower : ∃ L : ℝ, ∀ n, ∀ h ∈ K,
      -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖
        / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_log_norm_partitionFunctionComplexAlongExhaustion_div_card_le_lower_leeYang
      G Λ hBED hβ hJ hK hKsub hLower with ⟨C, hC⟩
  exact ⟨C, norm_freeEnergyComplexAlongExhaustion_le_of_abs_log_norm_bound_on_set_uniform
    G Λ β J hC⟩

/-- **Lee-Yang locally bounded family from polynomial-factor lower witnesses**:
on compact `K ⊆ leeYangDomain`, a stage-uniform lower normalised-log bound for
positive Lee-Yang polynomial-factor witnesses supplies the lower-log hypothesis
for `Z_ℂ`; combining this with the Lee-Yang upper bound gives a single
stage-independent free-energy bound `‖f_n(h)‖ ≤ C + π`.

This remains conditional on the polynomial-witness lower normalised-log input;
it only packages the route from that input to the locally bounded family. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J R : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hR : ∀ h ∈ K, |h.re| ≤ R)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  have hLower :
      ∃ L : ℝ, ∀ n, ∀ h ∈ K,
        -L ≤ Real.log ‖partitionFunctionComplexAlongExhaustion
            G Λ (J : ℂ) h (β : ℂ) n‖
          / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ) :=
    exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_of_poly_lower
      G Λ hβ.le hJ.le hR hPolyLower
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    G Λ hBED hβ hJ hK hKsub hLower

/-- **Compact Lee-Yang locally bounded family from polynomial lower witnesses**:
compactness supplies the real-part bound consumed by
`exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang`. The
polynomial-witness lower normalised-log input remains an explicit hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ K,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang
    G Λ hBED hβ hJ hK hKsub hR hPolyLower

/-- **Ball-local Lee-Yang locally bounded family from polynomial lower
witnesses**: if the polynomial-witness lower normalised-log input is available
on a closed ball contained in `leeYangDomain`, then the free-energy family is
bounded on the corresponding open ball. This is the local-cover shape used by
later normal-family/Vitali inputs. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain)
    (hPolyLower : ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
      ∃ ε : ℝ, 0 < ε ∧
        ε ≤ ‖(IsingModel.isingEdgePoly
          (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
            (Real.exp (-2 * β * J)))).eval
          (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
        -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_of_isCompact
      G Λ hBED hβ hJ (isCompact_closedBall h₀ ρ) hsub hPolyLower with ⟨C, hC⟩
  exact ⟨C, fun n h hh => hC n h (Metric.ball_subset_closedBall hh)⟩

/-- **Point-local Lee-Yang locally bounded family from polynomial lower
witnesses**: around any Lee-Yang point, choose a positive closed ball inside
`leeYangDomain`; a radius-dependent polynomial-witness lower normalised-log
input on that closed ball gives a bound on the corresponding open ball. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_around
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain)
    (hPolyLower : ∀ ρ : ℝ, 0 < ρ →
      Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain →
      ∃ Lε : ℝ, ∀ n, ∀ h ∈ Metric.closedBall h₀ ρ,
        ∃ ε : ℝ, 0 < ε ∧
          ε ≤ ‖(IsingModel.isingEdgePoly
            (IsingModel.graphToEdgeList (inducedGraph G (Λ.volume n))
              (Real.exp (-2 * β * J)))).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h)‖ ∧
          -Lε ≤ Real.log ε / (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases IsingModel.leeYangDomain_closedBall_subset hmem with ⟨ρ, hρ, hsub⟩
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_poly_lower_leeYang_on_ball
      G Λ hBED hβ hJ hsub (hPolyLower ρ hρ hsub) with ⟨C, hC⟩
  exact ⟨ρ, hρ, C, hC⟩

/-- **Compact Lee-Yang locally bounded family**: on compact
`K ⊆ leeYangDomain`, the root-product polynomial lower bound removes the
previous explicit polynomial-witness hypothesis and yields the uniform
free-energy bound `‖f_n(h)‖ ≤ C + π`. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ K,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_abs_re_le_on_isCompact hK with ⟨R, _hR_nonneg, hR⟩
  exact exists_norm_freeEnergyComplexAlongExhaustion_le_lower_log_leeYang
    G Λ hBED hβ hJ hK hKsub
    (exists_lower_log_norm_partitionFunctionComplexAlongExhaustion_leeYang_of_isCompact
      G Λ hβ hJ hK hKsub hR)

/-- **Ball-local Lee-Yang locally bounded family**: a closed ball contained in
`leeYangDomain` gives a uniform free-energy bound on the corresponding open
ball, with no remaining polynomial-witness hypothesis. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J ρ : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hsub : Metric.closedBall h₀ ρ ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
      G Λ hBED hβ hJ (isCompact_closedBall h₀ ρ) hsub with ⟨C, hC⟩
  exact ⟨C, fun n h hh => hC n h (Metric.ball_subset_closedBall hh)⟩

/-- **Point-local Lee-Yang locally bounded family**: every point of
`leeYangDomain` has a ball on which the free-energy family is uniformly
bounded, with the polynomial lower normalised-log input discharged by the
root-product estimate. -/
theorem exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_around
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n, ∀ h ∈ Metric.ball h₀ ρ,
      ‖freeEnergyComplexAlongExhaustion G Λ (J : ℂ) h (β : ℂ) n‖ ≤ C + Real.pi := by
  rcases IsingModel.leeYangDomain_closedBall_subset hmem with ⟨ρ, hρ, hsub⟩
  rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
      G Λ hBED hβ hJ hsub with ⟨C, hC⟩
  exact ⟨ρ, hρ, C, hC⟩

end Ambient

end IsingModel
