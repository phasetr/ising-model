import IsingModel.ContinuousSpin.TwoComponentGriffithsVI
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The doubled-rotated interaction expectation is non-negative (GJ Thm 4.7.1)

The dominated-convergence headline of the doubled-rotated cone: for a
non-negative-coefficient observable `obs` over `ι × Fin 4`, ferromagnetic
`β·J ≥ 0` and non-negative field `c_α, c_γ ≥ 0`,
`0 ≤ ∫_{(ι → Fin 4 → ℝ)} dSpinEval obs cfg · exp(βJ·∑_e edgeDot4 cfg e)
   · ∏ᵢ siteWeight4 A σ c_α c_γ (cfg i)`.

The interaction exponential is truncated to the non-negative-coefficient
`truncPoly4`, whose integral is `≥ 0` by `dSpinEval_integral_nonneg`; dominated
convergence with the uniform AM-GM dominator passes to the limit.  This is the
doubled-rotated non-negativity consumed by the duplicate-variable argument of the
second/third inequalities.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-- For a non-negative-coefficient polynomial, the evaluation is bounded in absolute
value by the evaluation at the absolute values. -/
theorem dSpinEval_abs_le {obs : MvPolynomial (ι × Fin 4) ℝ} (hobs : NNCoeffs obs)
    (cfg : ι → Fin 4 → ℝ) :
    |dSpinEval obs cfg| ≤ dSpinEval obs (fun i j => |cfg i j|) := by
  rw [dSpinEval, dSpinEval, eval_eq, eval_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [abs_mul, abs_of_nonneg (hobs d), Finset.abs_prod]
  refine congrArg _ (Finset.prod_congr rfl fun v _ => ?_)
  rw [abs_pow]
  simp only [dSpinVal]

/-- Integrability of the absolute monomial single-site doubled-rotated weight. -/
theorem integrable_abs_monomial_mul_siteWeight4 {A σ cα cγ : ℝ} (hA : 0 < A) (e : Fin 4 → ℕ) :
    Integrable (fun q : Fin 4 → ℝ => (∏ j, |q j| ^ e j) * siteWeight4 A σ cα cγ q) := by
  refine ((integrable_monomial_mul_siteWeight4
    (A := A) (σ := σ) (cα := cα) (cγ := cγ) hA e).norm).congr
    (Filter.Eventually.of_forall fun q => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (siteWeight4_pos A σ cα cγ q), Finset.abs_prod,
    abs_pow]

/-- Integrability of the absolute site-product over the doubled-rotated configuration. -/
theorem integrable_abs_dmonomial_mul_siteWeight4Prod [Fintype ι] {A σ cα cγ : ℝ} (hA : 0 < A)
    (a : ι → Fin 4 → ℕ) :
    Integrable (fun cfg : ι → Fin 4 → ℝ =>
      ∏ i, ((∏ j, |cfg i j| ^ a i j) * siteWeight4 A σ cα cγ (cfg i))) := by
  rw [volume_pi]
  exact Integrable.fintype_prod fun i => integrable_abs_monomial_mul_siteWeight4 hA (a i)

/-- Integrability of the dominating function `dSpinEval obs |cfg| · ∏ᵢ siteWeight4`. -/
theorem integrable_dSpinEvalAbs_siteWeight4Prod [Fintype ι] {A σ cα cγ : ℝ} (hA : 0 < A)
    (obs : MvPolynomial (ι × Fin 4) ℝ) :
    Integrable (fun cfg : ι → Fin 4 → ℝ =>
      dSpinEval obs (fun i j => |cfg i j|) * ∏ i, siteWeight4 A σ cα cγ (cfg i)) := by
  classical
  have hpt : ∀ cfg : ι → Fin 4 → ℝ,
      dSpinEval obs (fun i j => |cfg i j|) * ∏ i, siteWeight4 A σ cα cγ (cfg i)
        = ∑ d ∈ obs.support, obs.coeff d *
            ∏ i, ((∏ j, |cfg i j| ^ d (i, j)) * siteWeight4 A σ cα cγ (cfg i)) := by
    intro cfg
    rw [dSpinEval, eval_eq', Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_assoc]
    congr 1
    rw [Fintype.prod_prod_type (f := fun v => dSpinVal (fun i j => |cfg i j|) v ^ d v),
      ← Finset.prod_mul_distrib]
    simp only [dSpinVal]
  simp_rw [hpt]
  refine integrable_finset_sum _ fun d _ => ?_
  exact (integrable_abs_dmonomial_mul_siteWeight4Prod hA (fun i j => d (i, j))).const_mul _

/-- `dSpinEval p` is continuous in the configuration. -/
theorem continuous_dSpinEval (p : MvPolynomial (ι × Fin 4) ℝ) :
    Continuous (fun cfg : ι → Fin 4 → ℝ => dSpinEval p cfg) :=
  (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun v => (continuous_apply v.2).comp (continuous_apply v.1))

/-- `edgeDot4 · e` is continuous in the configuration. -/
theorem continuous_edgeDot4 (e : Sym2 ι) :
    Continuous (fun cfg : ι → Fin 4 → ℝ => edgeDot4 cfg e) := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [edgeDot4, Sym2.lift_mk, dDot4]
    fun_prop

/-- **The doubled-rotated interaction expectation of a non-negative-coefficient
observable is non-negative** (GJ Theorem 4.7.1 (4.7.6)–(4.7.8), pp. 70–71). -/
theorem dRotInteraction_nonneg [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : ℝ} {σ J β cα cγ : ℝ} (hA : 0 < A) (hβJ : 0 ≤ β * J) (hcα : 0 ≤ cα) (hcγ : 0 ≤ cγ)
    {obs : MvPolynomial (ι × Fin 4) ℝ} (hobs : NNCoeffs obs) :
    0 ≤ ∫ cfg : ι → Fin 4 → ℝ, dSpinEval obs cfg
      * Real.exp (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)
      * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
  classical
  set fN : ℕ → (ι → Fin 4 → ℝ) → ℝ := fun N cfg =>
    dSpinEval obs cfg * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)
      * ∏ i, siteWeight4 A σ cα cγ (cfg i) with hfN
  have hge : ∀ N, 0 ≤ ∫ cfg, fN N cfg := by
    intro N
    have heq : ∀ cfg : ι → Fin 4 → ℝ,
        fN N cfg = dSpinEval (truncPoly4 G obs J β N) cfg * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
      intro cfg; rw [hfN, dSpinEval_truncPoly4]
    simp_rw [heq]
    exact dSpinEval_integral_nonneg hA hcα hcγ (truncPoly4_nncoeffs G hobs hβJ N)
  set cc : ℝ := |β * J| * (G.edgeFinset.card : ℝ) with hcc
  have hlim : Filter.Tendsto (fun N => ∫ cfg, fN N cfg) Filter.atTop
      (nhds (∫ cfg : ι → Fin 4 → ℝ, dSpinEval obs cfg
        * Real.exp (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)
        * ∏ i, siteWeight4 A σ cα cγ (cfg i))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun cfg => dSpinEval obs (fun i j => |cfg i j|) * ∏ i, siteWeight4 A (σ - cc) cα cγ (cfg i))
      (fun N => ?_) (integrable_dSpinEvalAbs_siteWeight4Prod hA obs) (fun N => ?_) ?_
    · -- measurability
      have hc : Continuous (fN N) := by
        simp only [hfN]
        refine ((continuous_dSpinEval obs).mul ((continuous_expTrunc N).comp
          (continuous_const.mul (continuous_finset_sum _ fun e _ => continuous_edgeDot4 e)))).mul
          (continuous_finset_prod _ fun i _ => (continuous_siteWeight4 A σ cα cγ).comp
            (continuous_apply i))
      exact hc.aestronglyMeasurable
    · -- pointwise bound
      refine Filter.Eventually.of_forall fun cfg => ?_
      rw [hfN]
      have hWpos : ∀ i, (0 : ℝ) < siteWeight4 A σ cα cγ (cfg i) :=
        fun i => siteWeight4_pos _ _ _ _ _
      have hnorm : ‖dSpinEval obs cfg
            * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)
            * ∏ i, siteWeight4 A σ cα cγ (cfg i)‖
          = |dSpinEval obs cfg| * |expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)|
            * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (Finset.prod_pos fun i _ => hWpos i)]
      rw [hnorm]
      -- bound |expTrunc| ≤ exp(cc·∑normSq4)
      have hEN : |expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)|
          ≤ Real.exp (cc * ∑ i, normSq4 (cfg i)) := by
        calc |expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)|
            ≤ Real.exp |β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e| := abs_expTrunc_le_exp_abs _ _
          _ ≤ Real.exp (cc * ∑ i, normSq4 (cfg i)) := by
              refine Real.exp_le_exp.mpr ?_
              calc |β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e|
                  = |β * J| * |∑ e ∈ G.edgeFinset, edgeDot4 cfg e| := by rw [abs_mul]
                _ ≤ |β * J| * ∑ e ∈ G.edgeFinset, |edgeDot4 cfg e| :=
                    mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
                _ ≤ |β * J| * ∑ _e ∈ G.edgeFinset, ∑ i, normSq4 (cfg i) :=
                    mul_le_mul_of_nonneg_left
                      (Finset.sum_le_sum fun e _ => abs_edgeDot4_le_sum cfg e) (abs_nonneg _)
                _ = cc * ∑ i, normSq4 (cfg i) := by
                    rw [Finset.sum_const, nsmul_eq_mul, hcc]; ring
      have hsw : ∏ i, siteWeight4 A (σ - cc) cα cγ (cfg i)
          = Real.exp (cc * ∑ i, normSq4 (cfg i)) * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
        rw [Finset.prod_congr rfl fun i _ => siteWeight4_shift A σ cc cα cγ (cfg i),
          Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      calc |dSpinEval obs cfg| * |expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e)|
              * ∏ i, siteWeight4 A σ cα cγ (cfg i)
          ≤ dSpinEval obs (fun i j => |cfg i j|)
              * Real.exp (cc * ∑ i, normSq4 (cfg i)) * ∏ i, siteWeight4 A σ cα cγ (cfg i) := by
            refine mul_le_mul (mul_le_mul (dSpinEval_abs_le hobs cfg) hEN (abs_nonneg _) ?_)
              le_rfl (Finset.prod_nonneg fun i _ => (hWpos i).le) ?_
            · exact le_trans (abs_nonneg _) (dSpinEval_abs_le hobs cfg)
            · exact mul_nonneg (le_trans (abs_nonneg _) (dSpinEval_abs_le hobs cfg))
                (Real.exp_pos _).le
        _ = dSpinEval obs (fun i j => |cfg i j|) * ∏ i, siteWeight4 A (σ - cc) cα cγ (cfg i) := by
            rw [hsw]; ring
    · -- pointwise convergence
      refine Filter.Eventually.of_forall fun cfg => ?_
      rw [hfN]
      exact (tendsto_const_nhds.mul (tendsto_expTrunc _)).mul tendsto_const_nhds
  exact ge_of_tendsto' hlim hge

end IsingModel.ContinuousSpin
