import IsingModel.ContinuousSpin.TwoComponentGriffithsV

/-!
# The doubled-rotated interaction expectation (GJ Theorem 4.7.1, second/third)

The ferromagnetic interaction layer over the doubled-rotated cone of
`TwoComponentGriffithsV.lean`: for a non-negative-coefficient observable
polynomial `obs` over `ι × Fin 4`, ferromagnetic `βJ ≥ 0` and non-negative field
`c_α, c_γ ≥ 0`,
`0 ≤ ∫_{(ι → Fin 4 → ℝ)} dSpinEval obs cfg · exp(βJ·∑_e (αᵢαⱼ+βᵢβⱼ+γᵢγⱼ+δᵢδⱼ))
   · ∏ᵢ siteWeight4 A σ c_α c_γ (cfg i)`.

The interaction exponential is truncated to a non-negative-coefficient polynomial
(`truncPoly4`), whose integral is `≥ 0` by `dSpinEval_integral_nonneg`; dominated
convergence (with a uniform AM-GM dominator) passes to the limit.  This is the
doubled-rotated non-negativity consumed by the duplicate-variable argument.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-! ## The doubled-rotated interaction -/

/-- The doubled-rotated inner product `∑ₖ cfg i k · cfg j k` of two sites. -/
def dDot4 (cfg : ι → Fin 4 → ℝ) (i j : ι) : ℝ := ∑ k : Fin 4, cfg i k * cfg j k

/-- The per-edge doubled-rotated inner product on `Sym2 ι`. -/
noncomputable def edgeDot4 (cfg : ι → Fin 4 → ℝ) : Sym2 ι → ℝ :=
  Sym2.lift ⟨dDot4 cfg,
    fun i j => by simp only [dDot4]; exact Finset.sum_congr rfl fun k _ => by ring⟩

/-- The per-edge interaction polynomial `∑ₖ X(i,k)·X(j,k)`. -/
noncomputable def edgeDot4Poly (e : Sym2 ι) : MvPolynomial (ι × Fin 4) ℝ :=
  Sym2.lift ⟨fun i j => ∑ k : Fin 4, X (i, k) * X (j, k),
    fun i j => by exact Finset.sum_congr rfl fun k _ => by ring⟩ e

/-- The interaction-sum polynomial `S = ∑_e edgeDot4Poly e`. -/
noncomputable def interactionPoly4 (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MvPolynomial (ι × Fin 4) ℝ :=
  ∑ e ∈ G.edgeFinset, edgeDot4Poly e

/-- The truncated doubled-rotated integrand polynomial. -/
noncomputable def truncPoly4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (obs : MvPolynomial (ι × Fin 4) ℝ) (J β : ℝ) (N : ℕ) : MvPolynomial (ι × Fin 4) ℝ :=
  obs * ∑ k ∈ Finset.range N, C ((β * J) ^ k / k.factorial) * interactionPoly4 G ^ k

@[simp] theorem dSpinEval_X (v : ι × Fin 4) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (X v : MvPolynomial (ι × Fin 4) ℝ) cfg = cfg v.1 v.2 := by
  simp [dSpinEval, dSpinVal]

/-- `dSpinEval (edgeDot4Poly e)` is the per-edge inner product `edgeDot4`. -/
theorem dSpinEval_edgeDot4Poly (e : Sym2 ι) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (edgeDot4Poly e) cfg = edgeDot4 cfg e := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [edgeDot4Poly, Sym2.lift_mk, dSpinEval, map_sum, map_mul, eval_X, edgeDot4,
      dDot4, dSpinVal]

/-- `dSpinEval (interactionPoly4 G)` is the interaction sum. -/
theorem dSpinEval_interactionPoly4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (interactionPoly4 G) cfg = ∑ e ∈ G.edgeFinset, edgeDot4 cfg e := by
  rw [interactionPoly4, dSpinEval, map_sum]
  exact Finset.sum_congr rfl fun e _ => dSpinEval_edgeDot4Poly e cfg

/-- **`dSpinEval (truncPoly4 …)` is the truncated integrand**. -/
theorem dSpinEval_truncPoly4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (obs : MvPolynomial (ι × Fin 4) ℝ) (J β : ℝ) (N : ℕ) (cfg : ι → Fin 4 → ℝ) :
    dSpinEval (truncPoly4 G obs J β N) cfg
      = dSpinEval obs cfg * expTrunc N (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e) := by
  rw [truncPoly4, dSpinEval, map_mul, ← dSpinEval]
  congr 1
  rw [map_sum, expTrunc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, eval_C, ← dSpinEval, dSpinEval_interactionPoly4, mul_pow]
  ring

/-- The per-edge interaction polynomial has non-negative coefficients. -/
theorem edgeDot4Poly_nncoeffs (e : Sym2 ι) : NNCoeffs (edgeDot4Poly e) := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [edgeDot4Poly, Sym2.lift_mk]
    exact NNCoeffs.sum fun k _ => (NNCoeffs.X _).mul (NNCoeffs.X _)

/-- The truncating polynomial has non-negative coefficients (ferromagnetic `β, J ≥ 0`,
non-negative observable). -/
theorem truncPoly4_nncoeffs (G : SimpleGraph ι) [Fintype G.edgeSet]
    {obs : MvPolynomial (ι × Fin 4) ℝ} (hobs : NNCoeffs obs) {J β : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (N : ℕ) : NNCoeffs (truncPoly4 G obs J β N) := by
  have hinter : NNCoeffs (interactionPoly4 G) :=
    NNCoeffs.sum fun e _ => edgeDot4Poly_nncoeffs e
  rw [truncPoly4]
  refine hobs.mul (NNCoeffs.sum fun k _ => ?_)
  exact (NNCoeffs.C (div_nonneg (pow_nonneg (mul_nonneg hβ hJ) k) (by positivity))).mul
    (hinter.pow k)

/-! ## The dominated-convergence headline -/

/-- The squared norm `∑ₖ qₖ²` of a single rotated site. -/
def normSq4 (q : Fin 4 → ℝ) : ℝ := ∑ k : Fin 4, q k ^ 2

/-- Shifting the quadratic coefficient of the doubled-rotated site weight. -/
theorem siteWeight4_shift (A σ cc cα cγ : ℝ) (q : Fin 4 → ℝ) :
    siteWeight4 A (σ - cc) cα cγ q = Real.exp (cc * normSq4 q) * siteWeight4 A σ cα cγ q := by
  rw [siteWeight4, siteWeight4,
    rotSiteDensity_shift A σ cc q, normSq4, Fin.sum_univ_four]
  ring

/-- The single-site squared norm is non-negative. -/
theorem normSq4_nonneg (q : Fin 4 → ℝ) : 0 ≤ normSq4 q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **AM-GM bound for the per-edge interaction**: `|edgeDot4 cfg e| ≤ ∑ᵢ normSq4 (cfg i)`. -/
theorem abs_edgeDot4_le_sum [Fintype ι] (cfg : ι → Fin 4 → ℝ) (e : Sym2 ι) :
    |edgeDot4 cfg e| ≤ ∑ i, normSq4 (cfg i) := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [edgeDot4, Sym2.lift_mk, dDot4]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∑ k, |cfg i k * cfg j k| ≤ (normSq4 (cfg i) + normSq4 (cfg j)) / 2 := by
      rw [normSq4, normSq4, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul]
      nlinarith [sq_nonneg (|cfg i k| - |cfg j k|), sq_abs (cfg i k), sq_abs (cfg j k),
        abs_nonneg (cfg i k), abs_nonneg (cfg j k)]
    have hi : normSq4 (cfg i) ≤ ∑ m, normSq4 (cfg m) :=
      Finset.single_le_sum (fun m _ => normSq4_nonneg (cfg m)) (Finset.mem_univ i)
    have hj : normSq4 (cfg j) ≤ ∑ m, normSq4 (cfg m) :=
      Finset.single_le_sum (fun m _ => normSq4_nonneg (cfg m)) (Finset.mem_univ j)
    linarith [hstep, hi, hj]

end IsingModel.ContinuousSpin
