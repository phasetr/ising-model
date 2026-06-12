import IsingModel.ContinuousSpin.TwoComponentSystem
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrability of the two-component multi-site Gibbs weight (GJ §4.7)

The multi-site Gibbs weight `exp(−β·H − ∑ᵢ P(ξᵢ))` of the two-component system
(GJ Theorem 4.7.1, p. 70) is integrable over `(ℝ × ℝ)^ι` when the quartic
coupling `A` is positive. The quartic single-spin term `A·|ξᵢ|⁴` dominates the
quadratic interaction `β·J·ξᵢ·ξⱼ` and the linear external field, so a uniform
arithmetic–geometric-mean estimate bounds the exponent by a constant plus a
*separated* per-site quadratic-minus-quartic form:

`−β·H − ∑ᵢ P(ξᵢ) ≤ K + ∑ᵢ (b·|ξᵢ|² − A·|ξᵢ|⁴)`,

with `K`, `b` independent of the configuration. The Gibbs weight is therefore
dominated by `exp K · ∏ᵢ exp(b·|ξᵢ|² − A·|ξᵢ|⁴)`, a product of integrable
single-spin densities, and `MeasureTheory.Integrable.fintype_prod` plus
`MeasureTheory.Integrable.mono'` deliver the integrability. As a consequence the
partition function is strictly positive, so the Gibbs measure is well defined.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, (4.7.2)–(4.7.3), p. 70
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory Set
open scoped ENNReal

/-! ## The modified single-spin density `exp(b·|ξ|² − A·|ξ|⁴)` -/

/-- **Radial integrability of the modified single-spin density**:
`r ↦ r·exp(b·r² − A·r⁴)` is integrable on `(0, ∞)` for any `b ∈ ℝ` when
`A > 0`. The quartic term dominates the quadratic one: completing the square
gives `b·r² − A·r⁴ ≤ b²/(2A) − (A/2)·r⁴`, and `r·exp(−(A/2)·r⁴)` is Mathlib's
super-Gaussian. -/
theorem integrableOn_radial_quad_quartic {A b : ℝ} (hA : 0 < A) :
    IntegrableOn (fun r : ℝ => r * Real.exp (b * r ^ 2 - A * r ^ 4)) (Ioi 0) := by
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hbase : IntegrableOn
      (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(A / 2) * r ^ (4 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by linarith)
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  have hbase' : IntegrableOn (fun r : ℝ => r * Real.exp (-(A / 2) * r ^ 4)) (Ioi 0) := by
    refine hbase.congr_fun (fun r hr => ?_) measurableSet_Ioi
    rw [Real.rpow_one, h4, Real.rpow_natCast]
  have hM : IntegrableOn
      (fun r : ℝ => Real.exp (b ^ 2 / (2 * A)) * (r * Real.exp (-(A / 2) * r ^ 4))) (Ioi 0) :=
    hbase'.const_mul _
  refine Integrable.mono' hM ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hr) (Real.exp_pos _).le)]
    have hid : b * r ^ 2 - A * r ^ 4
        = b ^ 2 / (2 * A) - (A / 2) * r ^ 4 - (A * r ^ 2 - b) ^ 2 / (2 * A) := by
      field_simp
      ring
    have key : b * r ^ 2 - A * r ^ 4 ≤ b ^ 2 / (2 * A) + (-(A / 2) * r ^ 4) := by
      rw [hid]
      have : 0 ≤ (A * r ^ 2 - b) ^ 2 / (2 * A) := div_nonneg (sq_nonneg _) (le_of_lt h2A)
      linarith
    calc r * Real.exp (b * r ^ 2 - A * r ^ 4)
        ≤ r * Real.exp (b ^ 2 / (2 * A) + (-(A / 2) * r ^ 4)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (le_of_lt hr)
      _ = Real.exp (b ^ 2 / (2 * A)) * (r * Real.exp (-(A / 2) * r ^ 4)) := by
          rw [Real.exp_add]; ring

/-- The modified `SO(2)`-invariant single-spin density `exp(b·|ξ|² − A·|ξ|⁴)`,
the dominating factor for the multi-site Gibbs weight. -/
noncomputable def modSpinDensity (b A : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  Real.exp (b * (ξ.1 ^ 2 + ξ.2 ^ 2) - A * (ξ.1 ^ 2 + ξ.2 ^ 2) ^ 2)

/-- The modified single-spin density is continuous. -/
theorem continuous_modSpinDensity (b A : ℝ) : Continuous (modSpinDensity b A) := by
  unfold modSpinDensity
  fun_prop

/-- In polar coordinates the modified density at `(r·cosθ, r·sinθ)` is
`exp(b·r² − A·r⁴)`. -/
theorem modSpinDensity_polarCoord_symm (b A : ℝ) (rθ : ℝ × ℝ) :
    modSpinDensity b A (polarCoord.symm rθ) = Real.exp (b * rθ.1 ^ 2 - A * rθ.1 ^ 4) := by
  obtain ⟨r, θ⟩ := rθ
  have hpolar : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
  rw [hpolar]
  unfold modSpinDensity
  have hnorm : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  rw [hnorm]
  congr 1
  ring

/-- **The modified single-spin density is integrable** over `ℝ²` for `A > 0`
and any `b ∈ ℝ`: in polar coordinates the radial integral is finite. -/
theorem integrable_modSpinDensity {b A : ℝ} (hA : 0 < A) :
    Integrable (modSpinDensity b A) := by
  have hmeas : AEStronglyMeasurable (modSpinDensity b A) volume :=
    (continuous_modSpinDensity b A).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] modSpinDensity b A :=
    Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le
  rw [← lintegral_ofReal_ne_top_iff_integrable hmeas hnn,
    ← lintegral_comp_polarCoord_symm
      (fun ξ => ENNReal.ofReal (modSpinDensity b A ξ))]
  set g : ℝ → ENNReal :=
    fun r => ENNReal.ofReal (r * Real.exp (b * r ^ 2 - A * r ^ 4)) with hg
  have hint_eq : ∀ rθ ∈ polarCoord.target,
      ENNReal.ofReal rθ.1 • ENNReal.ofReal (modSpinDensity b A (polarCoord.symm rθ))
        = g rθ.1 := by
    intro rθ hrθ
    rw [modSpinDensity_polarCoord_symm, smul_eq_mul, hg,
      ← ENNReal.ofReal_mul (le_of_lt hrθ.1)]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hint_eq,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl]
  have hrad : IntegrableOn
      (fun r : ℝ => r * Real.exp (b * r ^ 2 - A * r ^ 4)) (Ioi 0) :=
    integrableOn_radial_quad_quartic hA
  have hradnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun r : ℝ => r * Real.exp (b * r ^ 2 - A * r ^ 4) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr =>
      mul_nonneg (le_of_lt hr) (Real.exp_pos _).le)
  have hrad_fin : (∫⁻ r in Ioi (0 : ℝ), g r) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hrad.aestronglyMeasurable hradnn).mpr hrad
  have hgcont : Continuous fun r : ℝ => r * Real.exp (b * r ^ 2 - A * r ^ 4) := by
    fun_prop
  have hgmeas : Measurable g := by
    rw [hg]; exact hgcont.measurable.ennreal_ofReal
  have hfactor : (∫⁻ rθ in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g rθ.1)
      = volume (Ioo (-π) π) * ∫⁻ r in Ioi (0 : ℝ), g r := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      ← Measure.prod_restrict,
      lintegral_prod (fun rθ : ℝ × ℝ => g rθ.1)
        (hgmeas.comp measurable_fst).aemeasurable]
    simp_rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [lintegral_mul_const _ hgmeas, mul_comm]
  rw [hfactor]
  refine ENNReal.mul_ne_top ?_ hrad_fin
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-! ## The uniform arithmetic–geometric-mean exponent bound -/

variable {ι : Type*}

/-- The squared norm `|ξᵢ|² = tᵢ² + qᵢ²` of the spin at site `i`. -/
def normSq (ξ : VectorConfig ι) (i : ι) : ℝ := vSpinT ξ i ^ 2 + vSpinQ ξ i ^ 2

/-- The squared norm is non-negative. -/
theorem normSq_nonneg (ξ : VectorConfig ι) (i : ι) : 0 ≤ normSq ξ i := by
  unfold normSq; positivity

/-- A single squared norm is bounded by the total `∑ₖ |ξₖ|²`. -/
theorem normSq_le_sum [Fintype ι] (ξ : VectorConfig ι) (i : ι) :
    normSq ξ i ≤ ∑ k, normSq ξ k :=
  Finset.single_le_sum (fun k _ => normSq_nonneg ξ k) (Finset.mem_univ i)

/-- **Arithmetic–geometric-mean bound for the inner product**:
`|ξᵢ·ξⱼ| ≤ ∑ₖ |ξₖ|²`. Indeed `|ξᵢ·ξⱼ| ≤ (|ξᵢ|² + |ξⱼ|²)/2 ≤ ∑ₖ |ξₖ|²`. -/
theorem abs_vDot_le_sum_normSq [Fintype ι] (ξ : VectorConfig ι) (i j : ι) :
    |vDot ξ i j| ≤ ∑ k, normSq ξ k := by
  have hi := normSq_le_sum ξ i
  have hj := normSq_le_sum ξ j
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
  · simp only [vDot, normSq] at hi hj ⊢
    nlinarith [sq_nonneg (vSpinT ξ i - vSpinT ξ j), sq_nonneg (vSpinT ξ i + vSpinT ξ j),
      sq_nonneg (vSpinQ ξ i - vSpinQ ξ j), sq_nonneg (vSpinQ ξ i + vSpinQ ξ j), hi, hj]

/-- The per-edge inner product is bounded by the total `∑ₖ |ξₖ|²`. -/
theorem abs_vEdgeDot_le_sum_normSq [Fintype ι] (ξ : VectorConfig ι) (e : Sym2 ι) :
    |vEdgeDot ξ e| ≤ ∑ k, normSq ξ k := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [vEdgeDot, Sym2.lift_mk]
    exact abs_vDot_le_sum_normSq ξ i j

/-- The first spin component is bounded by `(1 + |ξᵢ|²)/2` (from `(|tᵢ|−1)² ≥ 0`). -/
theorem abs_vSpinT_le (ξ : VectorConfig ι) (i : ι) :
    |vSpinT ξ i| ≤ (1 + normSq ξ i) / 2 := by
  unfold normSq
  nlinarith [sq_nonneg (|vSpinT ξ i| - 1), sq_abs (vSpinT ξ i), sq_nonneg (vSpinQ ξ i),
    abs_nonneg (vSpinT ξ i)]

/-- The second spin component is bounded by `(1 + |ξᵢ|²)/2`. -/
theorem abs_vSpinQ_le (ξ : VectorConfig ι) (i : ι) :
    |vSpinQ ξ i| ≤ (1 + normSq ξ i) / 2 := by
  unfold normSq
  nlinarith [sq_nonneg (|vSpinQ ξ i| - 1), sq_abs (vSpinQ ξ i), sq_nonneg (vSpinT ξ i),
    abs_nonneg (vSpinQ ξ i)]

/-- The total first-component magnitude is bounded: `∑ᵢ |tᵢ| ≤ (n + ∑ᵢ |ξᵢ|²)/2`. -/
theorem abs_sum_vSpinT_le [Fintype ι] (ξ : VectorConfig ι) :
    ∑ i, |vSpinT ξ i| ≤ ((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2 := by
  calc ∑ i, |vSpinT ξ i|
      ≤ ∑ i, (1 + normSq ξ i) / 2 := Finset.sum_le_sum fun i _ => abs_vSpinT_le ξ i
    _ = ((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]

/-- The total second-component magnitude is bounded: `∑ᵢ |qᵢ| ≤ (n + ∑ᵢ |ξᵢ|²)/2`. -/
theorem abs_sum_vSpinQ_le [Fintype ι] (ξ : VectorConfig ι) :
    ∑ i, |vSpinQ ξ i| ≤ ((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2 := by
  calc ∑ i, |vSpinQ ξ i|
      ≤ ∑ i, (1 + normSq ξ i) / 2 := Finset.sum_le_sum fun i _ => abs_vSpinQ_le ξ i
    _ = ((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]

/-- **Uniform exponent bound** (the AM-GM heart of GJ §4.7 integrability):
the Gibbs exponent `−β·H − ∑ᵢ P(ξᵢ)` is dominated by a constant `K` plus a
separated per-site quadratic-minus-quartic form `∑ᵢ (b·|ξᵢ|² − A·|ξᵢ|⁴)`, with
`K` and `b` independent of the configuration. The interaction and external
field are absorbed into the per-site quadratic coefficient `b`. -/
theorem exists_vectorWeight_exponent_bound [Fintype ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (A σ J h1 h2 β : ℝ) :
    ∃ K b : ℝ, ∀ ξ : VectorConfig ι,
      -β * vectorHamiltonian G J h1 h2 ξ - vectorPotentialSum A σ ξ
        ≤ K + ∑ i, (b * normSq ξ i - A * (normSq ξ i) ^ 2) := by
  set Kw : ℝ := ((|β * h1| + |β * h2|) / 2) * (Fintype.card ι : ℝ) with hKw
  set bw : ℝ := |β * J| * (G.edgeFinset.card : ℝ) + (|β * h1| + |β * h2|) / 2 - σ with hbw
  refine ⟨Kw, bw, fun ξ => ?_⟩
  have hpot : ∑ i, twoCompPotential A σ (vSpinT ξ i) (vSpinQ ξ i)
      = A * (∑ i, (normSq ξ i) ^ 2) + σ * (∑ i, normSq ξ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [twoCompPotential, normSq]
  have hrhs : ∑ i, (bw * normSq ξ i - A * (normSq ξ i) ^ 2)
      = bw * (∑ i, normSq ξ i) - A * (∑ i, (normSq ξ i) ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have ha : β * J * (∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
      ≤ |β * J| * ((G.edgeFinset.card : ℝ) * (∑ i, normSq ξ i)) := by
    calc β * J * (∑ e ∈ G.edgeFinset, vEdgeDot ξ e)
        ≤ |β * J * (∑ e ∈ G.edgeFinset, vEdgeDot ξ e)| := le_abs_self _
      _ = |β * J| * |∑ e ∈ G.edgeFinset, vEdgeDot ξ e| := by rw [abs_mul]
      _ ≤ |β * J| * (∑ e ∈ G.edgeFinset, |vEdgeDot ξ e|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |β * J| * (∑ _e ∈ G.edgeFinset, (∑ i, normSq ξ i)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun e _ => abs_vEdgeDot_le_sum_normSq ξ e) (abs_nonneg _)
      _ = |β * J| * ((G.edgeFinset.card : ℝ) * (∑ i, normSq ξ i)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hT : β * h1 * (∑ i, vSpinT ξ i)
      ≤ |β * h1| * (((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2) := by
    calc β * h1 * (∑ i, vSpinT ξ i)
        ≤ |β * h1 * (∑ i, vSpinT ξ i)| := le_abs_self _
      _ = |β * h1| * |∑ i, vSpinT ξ i| := by rw [abs_mul]
      _ ≤ |β * h1| * (∑ i, |vSpinT ξ i|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |β * h1| * (((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2) :=
          mul_le_mul_of_nonneg_left (abs_sum_vSpinT_le ξ) (abs_nonneg _)
  have hQc : β * h2 * (∑ i, vSpinQ ξ i)
      ≤ |β * h2| * (((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2) := by
    calc β * h2 * (∑ i, vSpinQ ξ i)
        ≤ |β * h2 * (∑ i, vSpinQ ξ i)| := le_abs_self _
      _ = |β * h2| * |∑ i, vSpinQ ξ i| := by rw [abs_mul]
      _ ≤ |β * h2| * (∑ i, |vSpinQ ξ i|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |β * h2| * (((Fintype.card ι : ℝ) + ∑ i, normSq ξ i) / 2) :=
          mul_le_mul_of_nonneg_left (abs_sum_vSpinQ_le ξ) (abs_nonneg _)
  rw [vectorHamiltonian, vectorPotentialSum, hpot, hrhs, hKw, hbw]
  nlinarith [ha, hT, hQc]

/-! ## Integrability of the multi-site Gibbs weight -/

/-- **The two-component multi-site Gibbs weight is integrable** for `A > 0**.
The uniform AM-GM bound dominates `vectorWeight` by `exp K · ∏ᵢ
modSpinDensity b A (ξ i)`, a product of integrable single-spin densities;
`Integrable.fintype_prod` and `Integrable.mono'` finish. This makes the
partition function and Gibbs measure of Theorem 4.7.1 well defined. -/
theorem integrable_vectorWeight [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A) :
    Integrable (vectorWeight G A σ J h1 h2 β) := by
  obtain ⟨K, b, hbound⟩ := exists_vectorWeight_exponent_bound G A σ J h1 h2 β
  have hprod : Integrable (fun ξ : VectorConfig ι => ∏ i, modSpinDensity b A (ξ i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun _ => integrable_modSpinDensity hA
  have hdom : Integrable
      (fun ξ : VectorConfig ι => Real.exp K * ∏ i, modSpinDensity b A (ξ i)) :=
    hprod.const_mul _
  refine Integrable.mono' hdom
    (continuous_vectorWeight G A σ J h1 h2 β).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vectorWeight_pos G A σ J h1 h2 β ξ).le]
  have hprod_eq : (∏ i, modSpinDensity b A (ξ i))
      = Real.exp (∑ i, (b * normSq ξ i - A * (normSq ξ i) ^ 2)) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [modSpinDensity, normSq, vSpinT, vSpinQ]
  rw [hprod_eq, ← Real.exp_add, vectorWeight]
  exact Real.exp_le_exp.mpr (hbound ξ)

/-- **The two-component partition function is strictly positive** for `A > 0`:
the integrand is continuous, integrable, non-negative, and positive somewhere.
Hence the Gibbs expectation `⟨·⟩` of Theorem 4.7.1 is well defined. -/
theorem vectorPartition_pos [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    {A : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A) :
    0 < vectorPartition G A σ J h1 h2 β := by
  rw [vectorPartition]
  exact integral_pos_of_integrable_nonneg_nonzero
    (continuous_vectorWeight G A σ J h1 h2 β)
    (integrable_vectorWeight G σ J h1 h2 β hA)
    (fun ξ => (vectorWeight_pos G A σ J h1 h2 β ξ).le)
    (x := fun _ => (0, 0)) (vectorWeight_pos G A σ J h1 h2 β _).ne'

end IsingModel.ContinuousSpin
