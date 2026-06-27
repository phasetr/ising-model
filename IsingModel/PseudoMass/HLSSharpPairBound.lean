import IsingModel.PseudoMass.HLSCorrelationCapstone
import IsingModel.HLSConvolutionSharp

/-!
# Sharp distance-decaying HLS correlation pair-product bound (GJ §17.5 p. 312)

This module upgrades the *constant*-form HLS correlation pair-product capstone
`tsum_correlationInfinite_pair_product_le_HLS_const`
(`IsingModel/PseudoMass/HLSCorrelationCapstone.lean`) to the **sharp,
distance-decaying** form, using the sharp distance-dependent HLS convolution
bound `hls_conv_sharp_decay` (`IsingModel/HLSConvolutionSharp.lean`):

```
∑_z ⟨φ(x₀)φ(z)⟩ · ⟨φ(y₀)φ(z)⟩ ≤ K · (1 + d(x₀,y₀))^{−(2α−d)}
```

instead of the bare constant `K`. This is the GJ §17.5 p. 312 cross-product term
in the Lebowitz IIIb estimate; its decay in `d(x₀,y₀)` is what feeds the HLS
comparison form `|c'| ≤ K·c/m⁻^{2α}` of Theorem 17.5.1.

The two intermediate lemmas are generic:

* `summable_pow_neg_pair_translate` — summability of the pair kernel
  `(1+d(x,z))^{−α}(1+d(y,z))^{−α}` for `d < 2α` (AM–GM against the diagonal);
* `hls_conv_sharp_decay_real` — the real-valued (ℝ, not `ℝ≥0∞`) corollary of
  `hls_conv_sharp_decay`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Summability of the HLS pair kernel.**  For `d < 2α` the function
`z ↦ (1+d(x,z))^{−α}·(1+d(y,z))^{−α}` on `ℤ^d` is summable.

By AM–GM the pair kernel is dominated by the average of the two squared kernels
`((1+d(x,z))^{−2α} + (1+d(y,z))^{−2α})/2`, each summable by
`summable_pow_neg_translate` (needs `d < 2α`). -/
theorem summable_pow_neg_pair_translate {d : ℕ} (x y : Fin d → ℤ) {α : ℝ}
    (hα2 : (d : ℝ) < 2 * α) :
    Summable (fun z : Fin d → ℤ =>
      (1 + (latticeDistance d x z : ℝ)) ^ (-α) *
        (1 + (latticeDistance d y z : ℝ)) ^ (-α)) := by
  have hSx := summable_pow_neg_translate d x (γ := 2 * α) hα2
  have hSy := summable_pow_neg_translate d y (γ := 2 * α) hα2
  have h_avg := (hSx.add hSy).div_const 2
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) h_avg
  set a := (1 + (latticeDistance d x z : ℝ)) ^ (-α) with ha_def
  set b := (1 + (latticeDistance d y z : ℝ)) ^ (-α) with hb_def
  have ha2 : a ^ 2 = (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * α)) := by
    rw [ha_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; congr 1; ring
  have hb2 : b ^ 2 = (1 + (latticeDistance d y z : ℝ)) ^ (-(2 * α)) := by
    rw [hb_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; congr 1; ring
  nlinarith [sq_nonneg (a - b), ha2, hb2]

/-- **Real-valued sharp HLS convolution bound.**  For `d/2 < α < d` there is
`C > 0` such that for all `x y`,
`∑'_z (1+d(x,z))^{−α}(1+d(y,z))^{−α} ≤ C·(1+d(x,y))^{−(2α−d)}` (in `ℝ`).

This is the real corollary of the `ℝ≥0∞` capstone `hls_conv_sharp_decay`: the
summand is nonnegative and summable (`summable_pow_neg_pair_translate`), so
`ENNReal.ofReal` of the real sum equals the `ℝ≥0∞` sum, and the `ofReal`
inequality transfers back. -/
theorem hls_conv_sharp_decay_real {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hαnn : 0 ≤ α) (hα : α < (d : ℝ)) (hα2 : (d : ℝ) < 2 * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin d → ℤ,
      ∑' z : Fin d → ℤ,
        (1 + (latticeDistance d x z : ℝ)) ^ (-α) *
          (1 + (latticeDistance d y z : ℝ)) ^ (-α)
      ≤ C * (1 + (latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := hls_conv_sharp_decay hd hαnn hα hα2
  refine ⟨C, hCpos, fun x y => ?_⟩
  have hsum := summable_pow_neg_pair_translate x y hα2
  have hnn : ∀ z : Fin d → ℤ, 0 ≤
      (1 + (latticeDistance d x z : ℝ)) ^ (-α) *
        (1 + (latticeDistance d y z : ℝ)) ^ (-α) := fun z => by positivity
  have hdecay_nn : (0 : ℝ) ≤
      C * (1 + (latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ))) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg (by positivity) _)
  have step : ENNReal.ofReal (∑' z : Fin d → ℤ,
        (1 + (latticeDistance d x z : ℝ)) ^ (-α) *
          (1 + (latticeDistance d y z : ℝ)) ^ (-α))
      ≤ ENNReal.ofReal
          (C * (1 + (latticeDistance d x y : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum, ENNReal.ofReal_mul hCpos.le]
    refine le_trans (le_of_eq (tsum_congr (fun z => ?_))) (hC x y)
    rw [ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff hdecay_nn).mp step

/-- **Sharp distance-decaying HLS correlation pair-product capstone**
(GJ §17.5 p. 312).  Given a `PseudoMassLatticeDistanceBridge`, the cross-product
sum of two-point functions decays in `d(x₀,y₀)`:
```
∃ K > 0, ∑_z ⟨φ(x₀)φ(z)⟩·⟨φ(y₀)φ(z)⟩ ≤ K·(1+d(x₀,y₀))^{−(2α−d)}
```
for `d/2 < α < d` (i.e. `d < 2α` and `α < d`).

This sharpens `tsum_correlationInfinite_pair_product_le_HLS_const` (which only
gives the constant bound) by replacing the constant convolution input with the
sharp distance-dependent HLS bound `hls_conv_sharp_decay_real`.

Proof: the existing pointwise bridge majorant
`correlationInfinite_pair_product_le_pseudoMass_pair` gives
`⟨φ(x₀)φ(z)⟩·⟨φ(y₀)φ(z)⟩ ≤ 2/(1+(M·d(x₀,z))^α)·2/(1+(M·d(y₀,z))^α)`; the form
bridge `one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow`
turns this into `4·C²·(1+d(x₀,z))^{−α}(1+d(y₀,z))^{−α}` with
`C = max 1 (M^α)⁻¹·2^α`; summing and applying `hls_conv_sharp_decay_real` gives
the decay with `K = 4·C²·C_HLS`. -/
theorem tsum_correlationInfinite_pair_product_le_HLS_sharp_decay
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (hαd : d < 2 * α) (hαd2 : α < d) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr' d J β) :
    ∃ K : ℝ, 0 < K ∧ ∀ x₀ y₀ : Fin d → ℤ,
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K * (1 + (latticeDistance d x₀ y₀ : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  set M := bridge.M_inf with hM_def
  have hM_pos : 0 < M := bridge.M_inf_pos
  have hd_one : 1 ≤ d := le_of_lt (lt_of_le_of_lt hα hαd2)
  set C := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hC_def
  have hC_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (pow_pos (by norm_num) α)
  obtain ⟨Chls, hChls_pos, hChls⟩ := hls_conv_sharp_decay_real (d := d) hd_one
    (α := (α : ℝ)) (by positivity) (by exact_mod_cast hαd2) (by exact_mod_cast hαd)
  refine ⟨4 * C ^ 2 * Chls, by positivity, fun x₀ y₀ => ?_⟩
  set f : (Fin d → ℤ) → ℝ := fun z =>
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
    with hf_def
  -- pointwise: f z ≤ 4·C²·(1+d(x₀,z))^{−α}(1+d(y₀,z))^{−α}.
  have hpoint : ∀ z, f z ≤ 4 * C ^ 2 *
      ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
        (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))) := by
    intro z
    have h1 := correlationInfinite_pair_product_le_pseudoMass_pair hα hr' d J β bridge x₀ y₀ z
    have hdx_nn : (0 : ℝ) ≤ (latticeDistance d x₀ z : ℝ) := by exact_mod_cast Nat.zero_le _
    have hdy_nn : (0 : ℝ) ≤ (latticeDistance d y₀ z : ℝ) := by exact_mod_cast Nat.zero_le _
    have hpair := one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow
      (M := M) (tx := (latticeDistance d x₀ z : ℝ))
      (ty := (latticeDistance d y₀ z : ℝ)) (α := α) hM_pos hdx_nn hdy_nn
    have hdx_eq : 1 / (1 + (latticeDistance d x₀ z : ℝ)) ^ α
        = (1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) :=
      one_div_one_add_pow_eq_rpow_neg hdx_nn
    have hdy_eq : 1 / (1 + (latticeDistance d y₀ z : ℝ)) ^ α
        = (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ)) :=
      one_div_one_add_pow_eq_rpow_neg hdy_nn
    calc f z
        ≤ 2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
            (2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α)) := h1
      _ = 4 * (1 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
            (1 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α))) := by ring
      _ ≤ 4 * (C ^ 2 * (1 / (1 + (latticeDistance d x₀ z : ℝ)) ^ α *
            (1 / (1 + (latticeDistance d y₀ z : ℝ)) ^ α))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            rw [hC_def]; exact hpair
      _ = 4 * C ^ 2 *
            ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
              (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))) := by
            rw [hdx_eq, hdy_eq]; ring
  -- summability of `f` (comparison) and of the majorant.
  have hsum_rpow := summable_pow_neg_pair_translate (α := (α : ℝ)) x₀ y₀ (by exact_mod_cast hαd)
  have hg_summable : Summable (fun z : Fin d → ℤ => 4 * C ^ 2 *
      ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
        (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ)))) :=
    hsum_rpow.mul_left _
  have hf_nn : ∀ z, 0 ≤ f z := by
    intro z
    simp only [hf_def]
    exact mul_nonneg
      (Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _)
      (Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _)
  have hf_summable : Summable f := Summable.of_nonneg_of_le hf_nn hpoint hg_summable
  calc ∑' z, f z
      ≤ ∑' z : Fin d → ℤ, 4 * C ^ 2 *
          ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
            (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))) :=
        hf_summable.tsum_le_tsum hpoint hg_summable
    _ = 4 * C ^ 2 * ∑' z : Fin d → ℤ,
          ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
            (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))) := by rw [tsum_mul_left]
    _ ≤ 4 * C ^ 2 *
          (Chls * (1 + (latticeDistance d x₀ y₀ : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left (hChls x₀ y₀) (by positivity)
    _ = 4 * C ^ 2 * Chls *
          (1 + (latticeDistance d x₀ y₀ : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by ring

end Ambient
end IsingModel
