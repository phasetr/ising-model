import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Segment primitives on convex open sets (GJ §4.6 Thm 4.6.2 support)

A holomorphic function on a convex open set has a primitive, constructed as the integral along
straight segments from a base point and differentiated under the integral sign — no
Goursat-type rectangle/triangle input is needed (mathlib's `Complex.HasPrimitives` covers only
balls and `univ`):
`∂_w[(w-b)·f(b+t(w-b))] = f(b+t(w-b)) + t(w-b)·f'(b+t(w-b)) = d/dt[t·f(b+t(w-b))]`,
so the parametric derivative integrates to `f(w)` by the fundamental theorem of calculus.

* `segmentPrimitive` — the segment-integral primitive.
* `segmentPrimitive_base` — vanishing at the base point.
* `segmentPoint_mem` — convexity keeps segment points inside the set.
* `hasDerivAt_segmentPrimitive` — the primitive differentiates back to `f`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70 (branch coherence input).
-/

namespace IsingModel

open Metric Set MeasureTheory intervalIntegral

/-- **Segment primitive**: the integral of `f` along the straight segment from the base point
`b` to `z`, parametrised over `[0, 1]`. On a convex open set containing `b` and `z` this is a
primitive of `f` (`hasDerivAt_segmentPrimitive`). -/
noncomputable def segmentPrimitive (f : ℂ → ℂ) (b z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (z - b) * f (b + t * (z - b))

/-- **Base value of the segment primitive**: at the base point the integrand vanishes. -/
theorem segmentPrimitive_base (f : ℂ → ℂ) (b : ℂ) : segmentPrimitive f b b = 0 := by
  simp [segmentPrimitive]

/-- **Segment points stay inside a convex set**: for `b, w` in a convex set, every point
`b + t·(w - b)` with `t ∈ [0, 1]` lies in the set. -/
theorem segmentPoint_mem {U : Set ℂ} (hU : Convex ℝ U) {b w : ℂ} (hb : b ∈ U) (hw : w ∈ U)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    b + (t : ℂ) * (w - b) ∈ U := by
  have hrw : b + (t : ℂ) * (w - b) = (1 - t) • b + t • w := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hrw]
  exact hU hb hw (by linarith [ht.2]) ht.1 (by ring)

/-- **Derivative of the segment primitive**: on a convex open set, the segment primitive of a
differentiable function with continuous derivative differentiates back to the function. The
proof differentiates under the integral sign (dominated, with constant bound on a compact
tube around the segment) and evaluates the resulting integral by the fundamental theorem of
calculus via `t ↦ t·f(b + t(z-b))`; no Goursat-type theorem enters. -/
theorem hasDerivAt_segmentPrimitive {U : Set ℂ} (hU : Convex ℝ U) (hUo : IsOpen U)
    {f f' : ℂ → ℂ}
    (hf : ∀ w ∈ U, HasDerivAt f (f' w) w)
    (hf'c : ContinuousOn f' U)
    {b z : ℂ} (hb : b ∈ U) (hz : z ∈ U) :
    HasDerivAt (segmentPrimitive f b) (f z) z := by
  have hfc : ContinuousOn f U := fun w hw => (hf w hw).continuousAt.continuousWithinAt
  -- a closed ball around `z` inside `U`
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hUo.mem_nhds hz)
  -- segment points for parameters in the closed ball
  have hseg : ∀ w ∈ closedBall z ε, ∀ t ∈ Set.Icc (0:ℝ) 1, b + (t : ℂ) * (w - b) ∈ U :=
    fun w hw t ht => segmentPoint_mem hU hb (hball hw) ht
  -- the compact tube of all such segment points
  set T : Set ℂ :=
    (fun p : ℝ × ℂ => b + (p.1 : ℂ) * (p.2 - b)) '' (Set.Icc (0:ℝ) 1 ×ˢ closedBall z ε)
    with hT
  have hTcomp : IsCompact T := by
    rw [hT]
    exact (isCompact_Icc.prod (isCompact_closedBall z ε)).image (by fun_prop)
  have hTU : T ⊆ U := by
    rw [hT]
    rintro x ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact hseg w hw t ht
  have hmemT : ∀ w ∈ closedBall z ε, ∀ t ∈ Set.Icc (0:ℝ) 1,
      b + (t : ℂ) * (w - b) ∈ T := by
    intro w hw t ht
    rw [hT]
    exact ⟨(t, w), ⟨ht, hw⟩, rfl⟩
  -- bounds on the tube
  obtain ⟨C, hC⟩ := hTcomp.exists_bound_of_continuousOn (hfc.mono hTU)
  obtain ⟨C', hC'⟩ := hTcomp.exists_bound_of_continuousOn (hf'c.mono hTU)
  -- parametric integrand and its `w`-derivative
  set F : ℂ → ℝ → ℂ := fun w t => (w - b) * f (b + (t : ℂ) * (w - b)) with hF
  set F' : ℂ → ℝ → ℂ := fun w t =>
    f (b + (t : ℂ) * (w - b)) + (t : ℂ) * (w - b) * f' (b + (t : ℂ) * (w - b)) with hF'
  -- continuity of the path-composed maps in `t` on `[0, 1]`
  have hpathcont : ∀ w : ℂ, Continuous fun t : ℝ => b + (t : ℂ) * (w - b) := by
    intro w; fun_prop
  have hFcont : ∀ w ∈ closedBall z ε, ContinuousOn (F w) (Set.Icc (0:ℝ) 1) := by
    intro w hw
    rw [hF]
    exact continuousOn_const.mul
      (hfc.comp (hpathcont w).continuousOn fun t ht => hseg w hw t ht)
  have hF'cont : ∀ w ∈ closedBall z ε, ContinuousOn (F' w) (Set.Icc (0:ℝ) 1) := by
    intro w hw
    rw [hF']
    refine ContinuousOn.add
      (hfc.comp (hpathcont w).continuousOn fun t ht => hseg w hw t ht) ?_
    exact (Complex.continuous_ofReal.continuousOn.mul continuousOn_const).mul
      (hf'c.comp (hpathcont w).continuousOn fun t ht => hseg w hw t ht)
  have hzball : z ∈ closedBall z ε := mem_closedBall_self (le_of_lt hε)
  have hIoc_subset : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one]
    exact Set.Ioc_subset_Icc_self
  -- dominated differentiation under the integral sign
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (F := F) (F' := F') (x₀ := z)
    (a := 0) (b := 1)
    (bound := fun _ => C + (‖z - b‖ + ε) * C')
    (s := closedBall z ε)
    (closedBall_mem_nhds z hε)
    (by
      filter_upwards [closedBall_mem_nhds z hε] with w hw
      exact ((hFcont w hw).mono hIoc_subset).aestronglyMeasurable measurableSet_uIoc)
    (((hFcont z hzball).mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable)
    (((hF'cont z hzball).mono hIoc_subset).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht w hw => by
      have htI : t ∈ Set.Icc (0:ℝ) 1 := hIoc_subset ht
      have hp : b + (t : ℂ) * (w - b) ∈ T := hmemT w hw t htI
      have h1 : ‖f (b + (t : ℂ) * (w - b))‖ ≤ C := hC _ hp
      have h2 : ‖f' (b + (t : ℂ) * (w - b))‖ ≤ C' := hC' _ hp
      have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) h2
      have htabs : |t| ≤ 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        rw [abs_of_pos ht.1]
        exact ht.2
      have hwb : ‖w - b‖ ≤ ‖z - b‖ + ε := by
        calc ‖w - b‖ = ‖(w - z) + (z - b)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z - b‖ := norm_add_le _ _
          _ ≤ ε + ‖z - b‖ := by
              have := mem_closedBall_iff_norm.mp hw
              linarith
          _ = ‖z - b‖ + ε := by ring
      rw [hF']
      calc ‖f (b + (t : ℂ) * (w - b)) + (t : ℂ) * (w - b) * f' (b + (t : ℂ) * (w - b))‖
          ≤ ‖f (b + (t : ℂ) * (w - b))‖ + ‖(t : ℂ) * (w - b) * f' (b + (t : ℂ) * (w - b))‖ :=
            norm_add_le _ _
        _ ≤ C + |t| * ‖w - b‖ * ‖f' (b + (t : ℂ) * (w - b))‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add h1 le_rfl
        _ ≤ C + 1 * (‖z - b‖ + ε) * C' := by
            refine add_le_add le_rfl ?_
            have h3 : |t| * ‖w - b‖ ≤ 1 * (‖z - b‖ + ε) :=
              mul_le_mul htabs hwb (norm_nonneg _) zero_le_one
            exact mul_le_mul h3 h2 (norm_nonneg _)
              (by positivity)
        _ = C + (‖z - b‖ + ε) * C' := by ring)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t ht w hw => by
      have htI : t ∈ Set.Icc (0:ℝ) 1 := hIoc_subset ht
      have hp : b + (t : ℂ) * (w - b) ∈ U := hseg w hw t htI
      -- the affine path in `w` and its derivative
      have hpath : HasDerivAt (fun w : ℂ => b + (t : ℂ) * (w - b)) (t : ℂ) w := by
        simpa using (((hasDerivAt_id w).sub_const b).const_mul ((t : ℂ))).const_add b
      have hcomp : HasDerivAt (fun w : ℂ => f (b + (t : ℂ) * (w - b)))
          (f' (b + (t : ℂ) * (w - b)) * (t : ℂ)) w := by
        simpa [mul_comm] using (hf _ hp).scomp w hpath
      have hmul := ((hasDerivAt_id w).sub_const b).mul hcomp
      rw [hF, hF']
      convert hmul using 1
      simp only [id_eq]
      ring)
  -- evaluate the parametric-derivative integral by FTC
  have hψ : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (t : ℂ) * f (b + (t : ℂ) * (z - b))) (F' z t) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hp : b + (t : ℂ) * (z - b) ∈ U := hseg z hzball t ht
    -- complex chain and product rule for `w ↦ w·f(b + w(z-b))`, then restrict along `ofReal`
    have hpathC : HasDerivAt (fun w : ℂ => b + w * (z - b)) (z - b) ((t : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((t : ℝ) : ℂ)).mul_const (z - b)).const_add b
    have hcompC : HasDerivAt (fun w : ℂ => f (b + w * (z - b)))
        (f' (b + (t : ℂ) * (z - b)) * (z - b)) ((t : ℝ) : ℂ) :=
      HasDerivAt.comp ((t : ℝ) : ℂ) (hf _ hp) hpathC
    have heC := (hasDerivAt_id ((t : ℝ) : ℂ)).mul hcompC
    have hreal := heC.comp_ofReal
    rw [hF']
    convert hreal using 1
    simp only [id_eq]
    ring
  have hFTC : (∫ t in (0:ℝ)..1, F' z t) = f z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hψ
      (((hF'cont z hzball).mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable)]
    simp
  have hgoal := key.2
  rw [hFTC] at hgoal
  exact hgoal

end IsingModel
