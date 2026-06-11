import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranch

/-!
# Stage-uniform bounds for the global branch (GJ §4.6 Thm 4.6.2)

Centre-value norm bounds for the global stage branch, replacing the all-centre principal
normalisation in the Borel–Carathéodory supply (Issue #628, relaxed-normalisation
re-threading). The normalised logarithmic derivative `Z'/(N·Z)` is the derivative of *any*
local branch carrying the exponential identity, so the existing local-branch half-ball bounds
plus the Schwarz derivative estimate bound it stage-uniformly on quarter-balls; a finite
subcover bounds it on compacts; the segment-integral estimate then bounds the global branch's
centre values.

* `deriv_eq_globalLogDerivStage_of_exp_eq` — any exponential-identity branch has derivative
  `Z'/(N·Z)`.
* `exists_uniform_norm_globalLogDerivStage_on_isCompact` — stage-uniform bound on compacts.
* `exists_uniform_norm_globalBranchStage_at` — stage-uniform centre-value bound for the
  global branch.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Derivative transfer**: any branch satisfying the exponential partition-function identity
on a ball has derivative `Z'/(N·Z)` there — no normalisation is involved, and the
non-vanishing of `Z` on the ball is automatic from the identity. -/
theorem deriv_eq_globalLogDerivStage_of_exp_eq (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (J β : ℂ) (n : ℕ) {branch : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hana : AnalyticOnNhd ℂ branch (Metric.ball c R))
    (hexp : ∀ z ∈ Metric.ball c R,
      Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch z)
        = partitionFunctionComplexAlongExhaustion G Λ J z β n)
    {z : ℂ} (hz : z ∈ Metric.ball c R) :
    deriv branch z = globalLogDerivStage G Λ J β n z := by
  classical
  have hNne : ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZz : partitionFunctionComplexAlongExhaustion G Λ J z β n
      = Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch z) :=
    (hexp z hz).symm
  have hZne : partitionFunctionComplexAlongExhaustion G Λ J z β n ≠ 0 := by
    rw [hZz]; exact Complex.exp_ne_zero _
  have hbr : HasDerivAt branch (deriv branch z) z :=
    (hana z hz).differentiableAt.hasDerivAt
  have hexp' : HasDerivAt
      (fun w => Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch w))
      (Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch z) *
        ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * deriv branch z)) z :=
    (hbr.const_mul _).cexp
  have heq : (fun w => Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch w))
      =ᶠ[nhds z] fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hexp w hw
  have hZderiv : HasDerivAt (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n)
      (Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branch z) *
        ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * deriv branch z)) z :=
    hexp'.congr_of_eventuallyEq heq.symm
  have hZderiv' : HasDerivAt (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n)
      (deriv (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n) z) z :=
    ((IsingModel.partitionFunctionComplex_analyticAt_h
      (inducedGraph G (Λ.volume n)) J β z).differentiableAt).hasDerivAt
  have hkey : partitionFunctionComplexAlongExhaustion G Λ J z β n *
      ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * deriv branch z)
      = deriv (fun h => partitionFunctionComplexAlongExhaustion G Λ J h β n) z := by
    rw [hZz]
    exact hZderiv.unique hZderiv'
  rw [globalLogDerivStage, ← hkey]
  field_simp

/-- **Stage-uniform bound for `Z'/(N·Z)` on compacts** (ferromagnetic positive real
parameters, bounded edge density): cover the compact by quarter-balls of the existing
positive-real closed-ball branch data; on each, the half-ball Borel–Carathéodory branch bound
and the Schwarz derivative estimate bound the derivative of the local branch, which equals
`Z'/(N·Z)` by the derivative transfer. -/
theorem exists_uniform_norm_globalLogDerivStage_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {T : Set ℂ} (hT : IsCompact T) (hTsub : T ⊆ IsingModel.leeYangDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ z ∈ T,
      ‖globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n z‖ ≤ C := by
  classical
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with ⟨closedData⟩
  -- per-centre stage-uniform derivative bound on quarter-balls
  have hpt : ∀ x ∈ T, ∃ ρ : ℝ, 0 < ρ ∧ ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ n, ∀ ξ ∈ Metric.ball x ρ,
      ‖globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n ξ‖ ≤ Cx := by
    intro x hx
    set x' : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨x, hTsub hx⟩ with hx'
    obtain ⟨Cb, hCb0, hCb⟩ :=
      exists_uniform_branchFamily_bound_half G Λ hBED hβ hJ closedData x'
    set r : ℝ := closedData.data.branchData.radius x' with hr
    have hrpos : 0 < r := closedData.data.branchData.radius_pos x'
    refine ⟨r / 4, by linarith, 2 * Cb / (r / 4), by positivity, ?_⟩
    intro n ξ hξ
    -- the local branch on the half ball is bounded by `Cb`; Schwarz on the quarter ball
    have hana : AnalyticOnNhd ℂ (closedData.data.branchData.branchFamily x' n)
        (Metric.ball (x' : ℂ) (r / 2)) :=
      (closedData.data.branchData.branch_spec x' n).1.mono
        (Metric.ball_subset_ball (by linarith))
    have hbound : ∀ z ∈ Metric.ball (x' : ℂ) (r / 2),
        ‖closedData.data.branchData.branchFamily x' n z‖ ≤ Cb :=
      fun z hz => (hCb n z hz).1
    have hsub : Metric.ball ξ (r / 4) ⊆ Metric.ball (x' : ℂ) (r / 2) := by
      intro w hw
      have h1 : dist w ξ < r / 4 := hw
      have h2 : dist ξ (x' : ℂ) < r / 4 := hξ
      have := dist_triangle w ξ (x' : ℂ)
      exact mem_ball.mpr (by simp only [mem_ball] at *; linarith)
    have hderiv := norm_deriv_le_of_analyticOnNhd_of_bounded hana hbound
      (by linarith : (0:ℝ) < r / 4) hsub
    -- transfer the derivative to `Z'/(N·Z)`
    have hξr : ξ ∈ Metric.ball (x' : ℂ) r := by
      have : dist ξ (x' : ℂ) < r / 4 := hξ
      exact mem_ball.mpr (by linarith)
    have htrans := deriv_eq_globalLogDerivStage_of_exp_eq G Λ (J : ℂ) (β : ℂ) n
      (closedData.data.branchData.branch_spec x' n).1
      (closedData.data.branchData.branch_spec x' n).2 hξr
    rw [← htrans]
    exact hderiv
  -- finite subcover and the maximum constant
  choose! ρ hρpos Cx hCx0 hCx using hpt
  have hcover : T ⊆ ⋃ x ∈ T, Metric.ball x (ρ x) := by
    intro x hx
    exact Set.mem_biUnion hx (Metric.mem_ball_self (hρpos x hx))
  rcases hT.elim_finite_subcover_image (fun x _ => Metric.isOpen_ball) hcover with
    ⟨s, hsT, hsfin, hscover⟩
  set sf : Finset ℂ := hsfin.toFinset with hsf
  have hmem_sf : ∀ {x : ℂ}, x ∈ sf → x ∈ T := fun hxs =>
    hsT (hsfin.mem_toFinset.mp hxs)
  refine ⟨∑ x ∈ sf, Cx x,
    Finset.sum_nonneg fun x hxs => hCx0 x (hmem_sf hxs), ?_⟩
  intro n z hz
  obtain ⟨x, hxs, hzb⟩ := Set.mem_iUnion₂.mp (hscover hz)
  calc ‖globalLogDerivStage G Λ (J : ℂ) (β : ℂ) n z‖
      ≤ Cx x := hCx x (hsT hxs) n z hzb
    _ ≤ ∑ x ∈ sf, Cx x :=
        Finset.single_le_sum (fun y hys => hCx0 y (hmem_sf hys))
          (hsfin.mem_toFinset.mpr hxs)

/-- **Stage-uniform centre-value bound for the global branch**: the anchor value is the
principal free energy of the base point (bounded stage-uniformly by the unconditional compact
Lee-Yang bound), and the segment integral is bounded by the segment length times the
stage-uniform bound for `Z'/(N·Z)` on the compact segment. This replaces the all-centre
principal normalisation in the Borel–Carathéodory bound supply. -/
theorem exists_uniform_norm_globalBranchStage_at
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {b h₀ : ℂ} (hb : b ∈ IsingModel.leeYangDomain) (hh₀ : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m,
      ‖globalBranchStage G Λ (J : ℂ) (β : ℂ) b m h₀‖ ≤ B := by
  classical
  -- the anchor value bound
  obtain ⟨A, hA⟩ := exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    G Λ hBED hβ hJ isCompact_singleton (Set.singleton_subset_iff.mpr hb)
  -- the compact segment and the stage-uniform integrand bound
  set T : Set ℂ := (fun t : ℝ => b + (t : ℂ) * (h₀ - b)) '' Set.Icc (0 : ℝ) 1 with hT
  have hTcomp : IsCompact T := by
    rw [hT]
    exact isCompact_Icc.image (by fun_prop)
  have hTsub : T ⊆ IsingModel.leeYangDomain := by
    rw [hT]
    rintro x ⟨t, ht, rfl⟩
    exact IsingModel.segmentPoint_mem IsingModel.convex_leeYangDomain hb hh₀ ht
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_norm_globalLogDerivStage_on_isCompact G Λ hBED hβ hJ hTcomp hTsub
  refine ⟨(A + Real.pi) + ‖h₀ - b‖ * C, ?_, ?_⟩
  · have hA0 : 0 ≤ A + Real.pi :=
      le_trans (norm_nonneg _) (hA 0 b (Set.mem_singleton b))
    positivity
  intro m
  rw [globalBranchStage]
  refine le_trans (norm_add_le _ _) (add_le_add (hA m b (Set.mem_singleton b)) ?_)
  rw [segmentPrimitive]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(h₀ - b) * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) m (b + (t : ℂ) * (h₀ - b))‖
        ≤ ‖h₀ - b‖ * C := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem : b + (t : ℂ) * (h₀ - b) ∈ T := by
      rw [hT]
      exact ⟨t, ⟨le_of_lt ht.1, ht.2⟩, rfl⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC m _ hmem) (norm_nonneg _)
  calc ‖∫ t in (0 : ℝ)..1,
        (h₀ - b) * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) m (b + (t : ℂ) * (h₀ - b))‖
      ≤ ‖h₀ - b‖ * C * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ‖h₀ - b‖ * C := by simp

/-- **Stage-uniform bound for the global branch on compacts**: the segment tube over a
compact target is compact and stays in the convex domain, so the anchor bound plus the
segment-integral estimate is uniform over the target. -/
theorem exists_uniform_norm_globalBranchStage_on_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (hBED : BoundedEdgeDensity G Λ) {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {b : ℂ} (hb : b ∈ IsingModel.leeYangDomain)
    {T : Set ℂ} (hT : IsCompact T) (hTsub : T ⊆ IsingModel.leeYangDomain) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m, ∀ z ∈ T,
      ‖globalBranchStage G Λ (J : ℂ) (β : ℂ) b m z‖ ≤ B := by
  classical
  obtain ⟨A, hA⟩ := exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_of_isCompact
    G Λ hBED hβ hJ isCompact_singleton (Set.singleton_subset_iff.mpr hb)
  -- the compact segment tube over the target
  set S : Set ℂ := (fun q : ℝ × ℂ => b + (q.1 : ℂ) * (q.2 - b)) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ T) with hS
  have hScomp : IsCompact S := by
    rw [hS]
    exact (isCompact_Icc.prod hT).image (by fun_prop)
  have hSsub : S ⊆ IsingModel.leeYangDomain := by
    rw [hS]
    rintro x ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
    exact IsingModel.segmentPoint_mem IsingModel.convex_leeYangDomain hb (hTsub hz) ht
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_norm_globalLogDerivStage_on_isCompact G Λ hBED hβ hJ hScomp hSsub
  -- the displacement is bounded on the compact target
  obtain ⟨R₀, hR₀⟩ := hT.exists_bound_of_continuousOn
    ((continuous_id.sub continuous_const).continuousOn (s := T))
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ z ∈ T, ‖z - b‖ ≤ R := fun z hz =>
    le_trans (hR₀ z hz) (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  refine ⟨(A + Real.pi) + R * C, ?_, ?_⟩
  · have hA0 : 0 ≤ A + Real.pi :=
      le_trans (norm_nonneg _) (hA 0 b (Set.mem_singleton b))
    positivity
  intro m z hz
  rw [globalBranchStage]
  refine le_trans (norm_add_le _ _) (add_le_add (hA m b (Set.mem_singleton b)) ?_)
  rw [segmentPrimitive]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(z - b) * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) m (b + (t : ℂ) * (z - b))‖
        ≤ R * C := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem : b + (t : ℂ) * (z - b) ∈ S := by
      rw [hS]
      exact ⟨(t, z), ⟨⟨le_of_lt ht.1, ht.2⟩, hz⟩, rfl⟩
    rw [norm_mul]
    exact mul_le_mul (hR z hz) (hC m _ hmem) (norm_nonneg _) hR0
  calc ‖∫ t in (0 : ℝ)..1,
        (z - b) * globalLogDerivStage G Λ (J : ℂ) (β : ℂ) m (b + (t : ℂ) * (z - b))‖
      ≤ R * C * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = R * C := by simp

end Ambient

end IsingModel
