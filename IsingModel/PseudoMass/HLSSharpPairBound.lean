import IsingModel.PseudoMass.HLSCorrelationCapstone
import IsingModel.HLSConvolutionSharp
import IsingModel.Concrete.LatticeGraphBED.NeighborDegree

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

/-- **Neighbour-shift bound for the negative-power kernel.**  For `α ≥ 0` and
`v` adjacent to `u` in `latticeGraph d`, `(1+d(z,v))^{−α} ≤ 2^α·(1+d(z,u))^{−α}`.

Adjacency means `d(u,v) = 1`, so `d(z,u) ≤ d(z,v)+1` (triangle), hence
`(1+d(z,u))/2 ≤ 1+d(z,v)` and the antitone base shift `rpow_neg_half_le`
applies. -/
theorem pow_neg_neighbour_shift_le {d : ℕ} {α : ℝ} (hαnn : 0 ≤ α)
    (z u v : Fin d → ℤ) (hadj : (IsingModel.latticeGraph d).Adj u v) :
    (1 + (latticeDistance d z v : ℝ)) ^ (-α)
      ≤ (2 : ℝ) ^ α * (1 + (latticeDistance d z u : ℝ)) ^ (-α) := by
  have huv : latticeDistance d u v = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d u v).mp hadj
  have hvu : latticeDistance d v u = 1 := by rw [latticeDistance_comm]; exact huv
  have htri : latticeDistance d z u ≤ latticeDistance d z v + latticeDistance d v u :=
    latticeDistance_triangle d z v u
  have hle : (latticeDistance d z u : ℝ) ≤ (latticeDistance d z v : ℝ) + 1 := by
    have hnat : latticeDistance d z u ≤ latticeDistance d z v + 1 := by rw [hvu] at htri; exact htri
    exact_mod_cast hnat
  have hlow : (1 + (latticeDistance d z u : ℝ)) / 2 ≤ 1 + (latticeDistance d z v : ℝ) := by linarith
  exact rpow_neg_half_le hαnn (by positivity) hlow

/-- **Neighbour-sum bound for the negative-power kernel.**  For `α ≥ 0`, summing
the kernel over the `≤ 2d` neighbours of `u` is bounded by
`2d·2^α·(1+d(z,u))^{−α}`.

Each neighbour term is bounded by `2^α·(1+d(z,u))^{−α}`
(`pow_neg_neighbour_shift_le`) and there are at most `2d` of them
(`latticeGraph_degree_le`). -/
theorem neighborFinset_sum_pow_neg_le {d : ℕ} {α : ℝ} (hαnn : 0 ≤ α) (z u : Fin d → ℤ) :
    ∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
        (1 + (latticeDistance d z v : ℝ)) ^ (-α)
      ≤ 2 * (d : ℝ) * ((2 : ℝ) ^ α * (1 + (latticeDistance d z u : ℝ)) ^ (-α)) := by
  set M : ℝ := (2 : ℝ) ^ α * (1 + (latticeDistance d z u : ℝ)) ^ (-α) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hbound : ∀ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
      (1 + (latticeDistance d z v : ℝ)) ^ (-α) ≤ M := by
    intro v hv
    exact pow_neg_neighbour_shift_le hαnn z u v ((SimpleGraph.mem_neighborFinset _ _ _).mp hv)
  have hcard : ((IsingModel.latticeGraph d).neighborFinset u).card ≤ 2 * d := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact latticeGraph_degree_le d u
  calc ∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          (1 + (latticeDistance d z v : ℝ)) ^ (-α)
      ≤ ((IsingModel.latticeGraph d).neighborFinset u).card • M :=
        Finset.sum_le_card_nsmul _ _ M hbound
    _ = (((IsingModel.latticeGraph d).neighborFinset u).card : ℝ) * M := by rw [nsmul_eq_mul]
    _ ≤ 2 * (d : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right _ hMnn
        calc (((IsingModel.latticeGraph d).neighborFinset u).card : ℝ)
            ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hcard
          _ = 2 * (d : ℝ) := by push_cast; ring

/-- **Neighbour-shifted sharp convolution bound.**  For `d/2 < α < d` there is
`C > 0` such that for all `x z`,
`∑'_u (1+d(x,u))^{−α}·(∑_{v∼u}(1+d(z,v))^{−α}) ≤ C·(1+d(x,z))^{−(2α−d)}`.

The neighbour-sum is bounded by `2d·2^α·(1+d(z,u))^{−α}`
(`neighborFinset_sum_pow_neg_le`), reducing the sum to the sharp pair convolution
`hls_conv_sharp_decay_real`; `C = 2d·2^α·C_HLS`.  This is the analytic core that
turns the GJ p. 312 nearest-neighbour edge cross-sum into a distance-decaying
bound (the edge-sum → ordered-pair reduction is the subject of PR-next2b). -/
theorem tsum_mul_neighborFinset_sum_pow_neg_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hαnn : 0 ≤ α) (hα : α < (d : ℝ)) (hα2 : (d : ℝ) < 2 * α) :
    ∃ C : ℝ, 0 < C ∧ ∀ x z : Fin d → ℤ,
      ∑' u : Fin d → ℤ, (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-α))
        ≤ C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * α - (d : ℝ))) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨C0, hC0, hC0bd⟩ := hls_conv_sharp_decay_real hd hαnn hα hα2
  refine ⟨2 * (d : ℝ) * (2 : ℝ) ^ α * C0, by positivity, fun x z => ?_⟩
  have hbound : ∀ u : Fin d → ℤ,
      (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-α))
        ≤ 2 * (d : ℝ) * (2 : ℝ) ^ α *
            ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
              (1 + (latticeDistance d z u : ℝ)) ^ (-α)) := by
    intro u
    calc (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
            (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
              (1 + (latticeDistance d z v : ℝ)) ^ (-α))
        ≤ (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
            (2 * (d : ℝ) * ((2 : ℝ) ^ α * (1 + (latticeDistance d z u : ℝ)) ^ (-α))) := by
          exact mul_le_mul_of_nonneg_left (neighborFinset_sum_pow_neg_le hαnn z u) (by positivity)
      _ = 2 * (d : ℝ) * (2 : ℝ) ^ α *
            ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
              (1 + (latticeDistance d z u : ℝ)) ^ (-α)) := by ring
  have hsum_pair := summable_pow_neg_pair_translate x z hα2
  have hsum_rhs : Summable (fun u : Fin d → ℤ => 2 * (d : ℝ) * (2 : ℝ) ^ α *
      ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
        (1 + (latticeDistance d z u : ℝ)) ^ (-α))) := hsum_pair.mul_left _
  have hlhs_nn : ∀ u : Fin d → ℤ, 0 ≤
      (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          (1 + (latticeDistance d z v : ℝ)) ^ (-α)) := fun u => by positivity
  have hlhs_sum : Summable (fun u : Fin d → ℤ =>
      (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
        (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
          (1 + (latticeDistance d z v : ℝ)) ^ (-α))) :=
    Summable.of_nonneg_of_le hlhs_nn hbound hsum_rhs
  calc ∑' u : Fin d → ℤ, (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-α))
      ≤ ∑' u : Fin d → ℤ, 2 * (d : ℝ) * (2 : ℝ) ^ α *
          ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
            (1 + (latticeDistance d z u : ℝ)) ^ (-α)) :=
        hlhs_sum.tsum_le_tsum hbound hsum_rhs
    _ = 2 * (d : ℝ) * (2 : ℝ) ^ α * ∑' u : Fin d → ℤ,
          ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
            (1 + (latticeDistance d z u : ℝ)) ^ (-α)) := by rw [tsum_mul_left]
    _ ≤ 2 * (d : ℝ) * (2 : ℝ) ^ α *
          (C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * α - (d : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left (hC0bd x z) (by positivity)
    _ = 2 * (d : ℝ) * (2 : ℝ) ^ α * C0 *
          (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * α - (d : ℝ))) := by ring

/-- **Single-factor pseudo-mass majorant in `(1+dist)^{−α}` form.**  For a
`PseudoMassLatticeDistanceBridge`, every two-point function is dominated by
`2·C_f·(1+d(x,w))^{−α}` with `C_f = max 1 (M^α)⁻¹·2^α`.

For `x = w` the singleton correlation vanishes (`correlationInfinite_pair_self_h_zero`);
for `x ≠ w`, the bridge's active-range + `correlationInfinite_le_two_div_…` give
`≤ 2/(1+(m·r')^α)`, monotonicity in the denominator (using `M·d ≤ m·r'`) gives
`≤ 2/(1+(M·d)^α)`, and the form bridge
`one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow` converts to the
`(1+d)^{−α}` shape. -/
theorem correlationInfinite_le_maj
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr' d J β)
    (x w : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, w}
      ≤ 2 * (max 1 (bridge.M_inf ^ α)⁻¹ * (2 : ℝ) ^ α) *
          (1 + (latticeDistance d x w : ℝ)) ^ (-(α : ℝ)) := by
  set M := bridge.M_inf with hM
  have hMpos : 0 < M := bridge.M_inf_pos
  set Cf := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hCf
  have hdw_nn : (0 : ℝ) ≤ (latticeDistance d x w : ℝ) := by positivity
  by_cases hxw : x = w
  · subst hxw
    rw [correlationInfinite_pair_self_h_zero d J β x]
    positivity
  · have hact := bridge.active x w hxw
    have h51 := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
      hα hr' (Ambient.cubicExhaustion d) J β x w hact
    have hbnd := bridge.bound x w hxw
    set m := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x w with hm
    have hMd_nn : (0 : ℝ) ≤ M * (latticeDistance d x w : ℝ) := by positivity
    have hmono : 2 / (1 + (m * r') ^ α)
        ≤ 2 / (1 + (M * (latticeDistance d x w : ℝ)) ^ α) := by
      apply div_le_div_of_nonneg_left (by norm_num)
      · have : (0 : ℝ) ≤ (M * (latticeDistance d x w : ℝ)) ^ α := pow_nonneg hMd_nn α
        linarith
      · have hpow : (M * (latticeDistance d x w : ℝ)) ^ α ≤ (m * r') ^ α :=
          pow_le_pow_left₀ hMd_nn hbnd α
        linarith
    have hform := one_div_one_add_M_t_pow_le_const_mul_one_div_one_add_pow_pow
      (M := M) (t := (latticeDistance d x w : ℝ)) (α := α) hMpos hdw_nn
    have hrpow : 1 / (1 + (latticeDistance d x w : ℝ)) ^ α
        = (1 + (latticeDistance d x w : ℝ)) ^ (-(α : ℝ)) :=
      one_div_one_add_pow_eq_rpow_neg hdw_nn
    calc Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, w}
        ≤ 2 / (1 + (m * r') ^ α) := h51
      _ ≤ 2 / (1 + (M * (latticeDistance d x w : ℝ)) ^ α) := hmono
      _ = 2 * (1 / (1 + (M * (latticeDistance d x w : ℝ)) ^ α)) := by ring
      _ ≤ 2 * (Cf * (1 / (1 + (latticeDistance d x w : ℝ)) ^ α)) := by
          rw [hCf]; exact mul_le_mul_of_nonneg_left hform (by norm_num)
      _ = 2 * Cf * (1 + (latticeDistance d x w : ℝ)) ^ (-(α : ℝ)) := by rw [hrpow]; ring

/-- **Summability of the neighbour-sum kernel.**  For `d < 2α`,
`u ↦ (1+d(x,u))^{−α}·(∑_{v∼u}(1+d(z,v))^{−α})` is summable, dominated by
`2d·2^α·(1+d(x,u))^{−α}(1+d(z,u))^{−α}` (`neighborFinset_sum_pow_neg_le`). -/
theorem summable_mul_neighborFinset_sum_pow_neg {d : ℕ} (x z : Fin d → ℤ) {α : ℝ}
    (hαnn : 0 ≤ α) (hα2 : (d : ℝ) < 2 * α) :
    Summable (fun u : Fin d → ℤ => (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
      (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
        (1 + (latticeDistance d z v : ℝ)) ^ (-α))) := by
  have hmaj : Summable (fun u : Fin d → ℤ => 2 * (d : ℝ) * (2 : ℝ) ^ α *
      ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
        (1 + (latticeDistance d z u : ℝ)) ^ (-α))) :=
    (summable_pow_neg_pair_translate x z hα2).mul_left _
  refine Summable.of_nonneg_of_le (fun u => by positivity) (fun u => ?_) hmaj
  calc (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
          (∑ v ∈ (IsingModel.latticeGraph d).neighborFinset u,
            (1 + (latticeDistance d z v : ℝ)) ^ (-α))
      ≤ (1 + (latticeDistance d x u : ℝ)) ^ (-α) *
          (2 * (d : ℝ) * ((2 : ℝ) ^ α * (1 + (latticeDistance d z u : ℝ)) ^ (-α))) :=
        mul_le_mul_of_nonneg_left (neighborFinset_sum_pow_neg_le hαnn z u) (by positivity)
    _ = 2 * (d : ℝ) * (2 : ℝ) ^ α *
          ((1 + (latticeDistance d x u : ℝ)) ^ (-α) *
            (1 + (latticeDistance d z u : ℝ)) ^ (-α)) := by ring

/-- **Sharp distance-decay of the GJ p. 312 dart cross-sum.**  Given a
`PseudoMassLatticeDistanceBridge`, for `d/2 < α < d` there is a uniform `K > 0`
such that for all `x z` and exhaustion stage `n`,
```
∑_{δ : Dart(G_n)} ⟨φ(x)φ(δ.fst)⟩·⟨φ(z)φ(δ.snd)⟩ ≤ K·(1+d(x,z))^{−(2α−d)}
```
where `G_n = inducedGraph (latticeGraph d) (volume n)`.

This is the decaying bound on the main term of
`derivative_profile_cubic_le_infiniteVolume_lebowitz` (whose edge cross-sum equals
this dart sum via `sum_edgeFinset_sym2_lift_prod_eq_sum_dart`).  Proof: bound each
correlation by its `(1+dist)^{−α}` majorant (`correlationInfinite_le_maj`); the
dart sum factors over the first endpoint into `∑_u (1+d(x,u))^{−α}·∑_{δ.fst=u}…`
whose inner sum is `≤ ∑_{w∼u}(1+d(z,w))^{−α}` (the subtype neighbours inject into
the ambient neighbour Finset); reindexing the subtype sum to `ℤ^d` and bounding by
the tsum (`Finset.sum_le_tsum`) feeds `tsum_mul_neighborFinset_sum_pow_neg_le`;
`K = 4·C_f²·C_HLS`. -/
theorem darts_cross_sum_le_sharp_decay
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (hαd : d < 2 * α) (hαd2 : α < d) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr' d J β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x z : Fin d → ℤ) (n : ℕ),
      ∑ δ : (Ambient.inducedGraph (IsingModel.latticeGraph d)
              ((Ambient.cubicExhaustion d).volume n)).Dart,
          Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {x, δ.fst.val} *
            Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) {z, δ.snd.val}
        ≤ K * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
  classical
  set M := bridge.M_inf with hM
  set Cf := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hCf
  have hCf_pos : 0 < Cf := by
    rw [hCf]; exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (by positivity)
  have hd_one : 1 ≤ d := le_of_lt (lt_of_le_of_lt hα hαd2)
  obtain ⟨C0, hC0, hC0bd⟩ := tsum_mul_neighborFinset_sum_pow_neg_le (d := d) hd_one
    (α := (α : ℝ)) (Nat.cast_nonneg α) (by exact_mod_cast hαd2) (by exact_mod_cast hαd)
  have hsummable : ∀ x z : Fin d → ℤ, Summable (fun u : Fin d → ℤ =>
      (1 + (latticeDistance d x u : ℝ)) ^ (-(α : ℝ)) *
        (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u,
          (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)))) := fun x z =>
    summable_mul_neighborFinset_sum_pow_neg x z (Nat.cast_nonneg α) (by exact_mod_cast hαd)
  refine ⟨4 * Cf ^ 2 * C0, by positivity, fun x z n => ?_⟩
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Ambient.cubicExhaustion d).volume n) with hG
  -- majorant abbreviations
  set A : ↑((Ambient.cubicExhaustion d).volume n) → ℝ :=
    fun u => (1 + (latticeDistance d x u.val : ℝ)) ^ (-(α : ℝ)) with hA
  set B : ↑((Ambient.cubicExhaustion d).volume n) → ℝ :=
    fun v => (1 + (latticeDistance d z v.val : ℝ)) ^ (-(α : ℝ)) with hB
  have hA_nn : ∀ u, 0 ≤ A u := fun u => by rw [hA]; positivity
  have hB_nn : ∀ v, 0 ≤ B v := fun v => by rw [hB]; positivity
  -- Step 1: per-dart correlation ≤ majorant product (×(2Cf)²).
  have hstep1 : ∑ δ : G.Dart,
        Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, δ.fst.val} *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, δ.snd.val}
      ≤ ∑ δ : G.Dart, (2 * Cf) ^ 2 * (A δ.fst * B δ.snd) := by
    apply Finset.sum_le_sum
    intro δ _
    have hx := correlationInfinite_le_maj hα hr' d J β bridge x δ.fst.val
    have hz := correlationInfinite_le_maj hα hr' d J β bridge z δ.snd.val
    have hxnn := Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf {x, δ.fst.val}
    have hznn := Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf {z, δ.snd.val}
    calc Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, δ.fst.val} *
          Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, δ.snd.val}
        ≤ (2 * Cf * A δ.fst) * (2 * Cf * B δ.snd) := by
          rw [hA, hB, hCf]
          exact mul_le_mul hx hz hznn (hxnn.trans hx)
      _ = (2 * Cf) ^ 2 * (A δ.fst * B δ.snd) := by ring
  -- Step 2: dart sum of majorant products ≤ (2Cf)² · ∑_u A u · (ambient neighbour B-sum).
  have hstep2 : ∑ δ : G.Dart, (2 * Cf) ^ 2 * (A δ.fst * B δ.snd)
      ≤ (2 * Cf) ^ 2 * ∑ u : ↑((Ambient.cubicExhaustion d).volume n),
          A u * (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u.val,
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ))) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun (δ : G.Dart) _ => Finset.mem_univ δ.fst) (fun δ => A δ.fst * B δ.snd)]
    apply Finset.sum_le_sum
    intro u _
    have hfac : ∑ δ ∈ Finset.univ.filter (fun δ : G.Dart => δ.fst = u), A δ.fst * B δ.snd
        = A u * ∑ δ ∈ Finset.univ.filter (fun δ : G.Dart => δ.fst = u), B δ.snd := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro δ hδ; rw [(Finset.mem_filter.mp hδ).2]
    rw [hfac]
    apply mul_le_mul_of_nonneg_left _ (hA_nn u)
    -- inner: ∑_{δ.fst=u} B δ.snd ≤ ∑_{w∈ambient nbr u.val} (1+d(z,w))^{-α}
    have hinj : ∀ δ₁ ∈ Finset.univ.filter (fun δ : G.Dart => δ.fst = u),
        ∀ δ₂ ∈ Finset.univ.filter (fun δ : G.Dart => δ.fst = u),
        (δ₁.snd.val) = (δ₂.snd.val) → δ₁ = δ₂ := by
      intro δ₁ h₁ δ₂ h₂ h
      exact SimpleGraph.Dart.ext _ _ (Prod.ext
        ((Finset.mem_filter.mp h₁).2.trans (Finset.mem_filter.mp h₂).2.symm)
        (Subtype.ext h))
    calc ∑ δ ∈ Finset.univ.filter (fun δ : G.Dart => δ.fst = u), B δ.snd
        = ∑ w ∈ (Finset.univ.filter (fun δ : G.Dart => δ.fst = u)).image (fun δ => δ.snd.val),
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u.val,
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => by positivity)
          intro w hw
          rw [Finset.mem_image] at hw
          obtain ⟨δ, hδ, rfl⟩ := hw
          rw [SimpleGraph.mem_neighborFinset]
          have hadj : G.Adj δ.fst δ.snd := δ.adj
          have hua : G.Adj u δ.snd := by rw [← (Finset.mem_filter.mp hδ).2]; exact hadj
          simp only [hG, Ambient.inducedGraph, SimpleGraph.induce_adj] at hua
          exact hua
  -- Step 3: reindex subtype sum to ℤ^d, bound by tsum, apply HLS.
  have hstep3 : (2 * Cf) ^ 2 * ∑ u : ↑((Ambient.cubicExhaustion d).volume n),
          A u * (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u.val,
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)))
      ≤ 4 * Cf ^ 2 * C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
    have hcoe : ∑ u : ↑((Ambient.cubicExhaustion d).volume n),
          A u * (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u.val,
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)))
        = ∑ u' ∈ (Ambient.cubicExhaustion d).volume n,
            (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
              (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
                (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ))) := by
      simp only [hA]
      exact Finset.sum_coe_sort ((Ambient.cubicExhaustion d).volume n)
        (fun u' => (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
          (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
            (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ))))
    rw [hcoe]
    have hfinle : ∑ u' ∈ (Ambient.cubicExhaustion d).volume n,
          (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
            (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
              (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)))
        ≤ ∑' u' : Fin d → ℤ, (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
              (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
                (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ))) :=
      (hsummable x z).sum_le_tsum _ (fun u' _ => by positivity)
    calc (2 * Cf) ^ 2 * ∑ u' ∈ (Ambient.cubicExhaustion d).volume n,
            (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
              (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
                (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ)))
        ≤ (2 * Cf) ^ 2 * ∑' u' : Fin d → ℤ, (1 + (latticeDistance d x u' : ℝ)) ^ (-(α : ℝ)) *
              (∑ w ∈ (IsingModel.latticeGraph d).neighborFinset u',
                (1 + (latticeDistance d z w : ℝ)) ^ (-(α : ℝ))) :=
          mul_le_mul_of_nonneg_left hfinle (by positivity)
      _ ≤ (2 * Cf) ^ 2 * (C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hC0bd x z) (by positivity)
      _ = 4 * Cf ^ 2 * C0 * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))) := by
          ring
  exact (hstep1.trans hstep2).trans hstep3

end Ambient
end IsingModel
