import IsingModel.PseudoMass.HLSCorrelationCapstone
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfileCubicPair
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.PolyDecay
import IsingModel.Conditioning.CorrelationRates.ExpRate
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor from a cubicTanhProfileBound family

Step 119 plan Step 5.7: concrete constructor for the abstract
`PseudoMassLatticeDistanceBridge` structure introduced in
`PseudoMass/HLSCorrelationCapstone.lean` (#3171). Given a family of anchored
`cubicTanhProfileBound` hypotheses (one per nonzero displacement) and a uniform
zero-anchored pseudo-mass lower bound `M_inf · d(0, w) ≤
pseudoMassFromParamsAtPair 0 w · r`, we produce the bridge as a single
`PseudoMassLatticeDistanceBridge` value, which can then be fed directly into
the HLS sum bound `tsum_correlationInfinite_pair_product_le_HLS_const`.

The lift from anchored to arbitrary distinct pairs uses translation invariance
of the ℤ^d Ising model under the cubic exhaustion: pair correlations only
depend on the displacement `z - x` via
`correlationInfinite_latticeGraph_pair_eq_twoPointFunction`, and lattice
distances on ℤ^d are translation invariant by `latticeDistance_translate_eq`.

This family-based constructor is kept as a compatibility interface for callers
that already have the all-displacement `cubicTanhProfileBound` family.  The
no-go facts in `CubicPseudoMassTanhProfileNoGo` show that this family cannot be
discharged from the elementary positive high-temperature assumptions alone; the
canonical forward route is the direct Simon-Lieb trichotomy bridge in
`HLSBridgeFromSimonLieb`.

The bridge constructor lives outside `IsingModel/PseudoMass/` to avoid an
import cycle: `LatticeMassPseudoMassTransferTanhPowDistCubicPair` (consumed
transitively via `CubicPseudoMassTanhProfileCubicPair`) imports
`IsingModel.PseudoMass`.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Translation reduction of the pair correlation** (Step 119 plan Step 5.7).

For ferromagnetic parameters and any pair `(x, z)`, the correlation
`correlationInfinite ⟨J,0,β⟩ {x, z}` equals the anchored correlation at the
displacement `{0, z - x}`. Direct consequence of
`correlationInfinite_latticeGraph_pair_eq_twoPointFunction` and
`twoPointFunction_apply`. -/
theorem correlationInfinite_pair_eq_displacement
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      = Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {(0 : Fin d → ℤ), z - x} := by
  have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have h := correlationInfinite_latticeGraph_pair_eq_twoPointFunction d
    (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  rw [h, twoPointFunction_apply]

/-- **Translation reduction of `pseudoMassFromParamsAtPair`** (Step 119 plan
Step 5.7).

`pseudoMassFromParamsAtPair` depends on the underlying correlation only, so
the translation reduction
`correlationInfinite ⟨J,0,β⟩ {x, z} = correlationInfinite ⟨J,0,β⟩ {0, z - x}`
lifts to a `pseudoMassFromParamsAtPair` identity. -/
theorem pseudoMassFromParamsAtPair_eq_displacement
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 (z - x) := by
  unfold pseudoMassFromParamsAtPair
  rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]

/-- **Active range from the cubicTanhProfileBound at the displacement**
(Step 119 plan Step 5.7).

For distinct `(x, z)`, given the anchored tanh-profile bound at the
displacement `z - x`, the pair correlation
`correlationInfinite ⟨J,0,β⟩ {x, z}` lies in the active range
`Ioo 0 2`. -/
theorem correlationInfinite_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound_displacement
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile_tanh : cubicTanhProfileBound α d r β J (z - x)) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 := by
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
  exact correlationInfinite_cubic_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound
    hr hJ hβ hlt hzx_ne hprofile_tanh

/-- **Lattice-distance translation form** (Step 119 plan Step 5.7).

`latticeDistance d x z = latticeDistance d 0 (z - x)`. Direct application of
`latticeDistance_translate_eq` (which lives in `PolyDecay.lean`). -/
theorem latticeDistance_pair_eq_displacement
    (d : ℕ) (x z : Fin d → ℤ) :
    latticeDistance d x z = latticeDistance d 0 (z - x) :=
  latticeDistance_translate_eq d x z

/-- **Bound lift from the zero-anchored uniform pseudo-mass lower bound**
(Step 119 plan Step 5.7).

If for every nonzero displacement `w` the zero-anchored pseudo-mass dominates
`M_inf · d(0, w)`, then for every distinct pair `(x, z)` the pair pseudo-mass
dominates `M_inf · d(x, z)`. Direct consequence of the translation reductions
`pseudoMassFromParamsAtPair_eq_displacement` and
`latticeDistance_pair_eq_displacement` at `w = z - x`. -/
theorem pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {M_inf : ℝ}
    (hbase : ∀ w : Fin d → ℤ, w ≠ 0 →
      M_inf * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M_inf * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  intro x z hxz
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have h_dist : (latticeDistance d x z : ℝ) = (latticeDistance d 0 (z - x) : ℝ) := by
    exact_mod_cast latticeDistance_pair_eq_displacement d x z
  have h_pseudo := pseudoMassFromParamsAtPair_eq_displacement hα hr d hJ hβ x z
  rw [h_dist, h_pseudo]
  exact hbase (z - x) hzx_ne

/-- **Active-range lift from a uniform `cubicTanhProfileBound` family**
(Step 119 plan Step 5.7).

If a `cubicTanhProfileBound` holds at every nonzero displacement, then the
pair correlation lies in the active range `Ioo 0 2` for every distinct pair
`(x, z)`.  This is a conditional compatibility wrapper; under the positive
high-temperature assumptions, `CubicPseudoMassTanhProfileNoGo` shows that the
all-displacement family itself is impossible. -/
theorem correlationInfinite_pair_active_of_cubicTanhProfileBound_family
    {α d : ℕ} {r : ℝ} (hr : 0 < r)
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (hfamily : ∀ w : Fin d → ℤ, w ≠ 0 → cubicTanhProfileBound α d r β J w) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  intro x z hxz
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  exact correlationInfinite_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound_displacement
    hr hJ hβ hlt hxz (hfamily (z - x) hzx_ne)

/-- **`PseudoMassLatticeDistanceBridge` constructor from a cubicTanhProfileBound
family** (Step 119 plan Step 5.7 capstone).

Given:

- ferromagnetic data `0 ≤ J`, `0 < β`, high-temperature constraint
  `β · J · 2d < 1`;
- positivity inputs `0 < r`, `0 < M_inf`;
- a uniform tanh-profile family providing `cubicTanhProfileBound α d r β J w`
  at every nonzero `w`;
- a zero-anchored pseudo-mass lower bound `M_inf · d(0, w) ≤
  pseudoMassFromParamsAtPair 0 w · r` for every nonzero `w`,

we construct the abstract `PseudoMassLatticeDistanceBridge` value required by
`tsum_correlationInfinite_pair_product_le_HLS_const`. The constructor itself
is purely a packaging step: all substantive content lies in the family inputs.
After `CubicPseudoMassTanhProfileNoGo`, this constructor should not be read as
a route for producing an input-free high-temperature bridge; use the direct
Simon-Lieb trichotomy constructors for that shape.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312. -/
noncomputable def PseudoMassLatticeDistanceBridge_of_cubicTanh_family
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    {M_inf : ℝ} (hM_pos : 0 < M_inf)
    (hfamily : ∀ w : Fin d → ℤ, w ≠ 0 → cubicTanhProfileBound α d r β J w)
    (hbase : ∀ w : Fin d → ℤ, w ≠ 0 →
      M_inf * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r) :
    PseudoMassLatticeDistanceBridge hα hr d J β where
  M_inf := M_inf
  M_inf_pos := hM_pos
  hf := ⟨hJ, le_refl 0, hβ⟩
  bound := pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ hbase
  active := correlationInfinite_pair_active_of_cubicTanhProfileBound_family
    hr hJ hβ hlt hfamily

/-- **`pseudoMassFromParamsAtPair` lower bound via a `pseudoMassG` upper bound on
the correlation** (Step 119 plan Step 5.7b).

If the correlation lies in the active range `Ioo 0 2` and is dominated by
`pseudoMassG α r t` for some `t ≥ 0`, then by the implicit-definition iff
`pseudoMass_ge_iff_pseudoMassG_ge` (`PseudoMass/Basic.lean`),
`t ≤ pseudoMassFromParamsAtPair`. This is the atomic reduction from the
analytic input `correlation ≤ pseudoMassG α r t` to the
`bridge.bound`-shaped conclusion. -/
theorem pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {t : ℝ} (ht : 0 ≤ t)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ pseudoMassG α r t) :
    t ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z := by
  unfold pseudoMassFromParamsAtPair
  rw [pseudoMassExt_of_mem hα hr hcorr]
  exact (pseudoMass_ge_iff_pseudoMassG_ge hα hr hcorr ht).mpr hle

/-- **`bridge.bound`-shape reduction at the zero-anchored displacement**
(Step 119 plan Step 5.7b).

Given the active range and the analytic input `correlation ≤
pseudoMassG α r (M · d(0, w) / r)`, conclude the zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.
Atomic building block for the `hbase` field of
`PseudoMassLatticeDistanceBridge_of_cubicTanh_family`. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (w : Fin d → ℤ)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ≤ pseudoMassG α r (M * (latticeDistance d 0 w : ℝ) / r)) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  set t : ℝ := M * (latticeDistance d 0 w : ℝ) / r with ht_def
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have ht_nn : 0 ≤ t := by
    apply div_nonneg
    · exact mul_nonneg hM hdist_nn
    · exact hr.le
  have h_pm_ge : t ≤ pseudoMassFromParamsAtPair hα hr d Λ p 0 w :=
    pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG
      hα hr d Λ p 0 w ht_nn hcorr hle
  have h_mul : t * r = M * (latticeDistance d 0 w : ℝ) := by
    rw [ht_def, div_mul_cancel₀ _ (ne_of_gt hr)]
  have h_step : t * r ≤ pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r :=
    mul_le_mul_of_nonneg_right h_pm_ge hr.le
  linarith [h_step, h_mul.symm.le, h_mul.le]

/-! ## Step 119 plan Step 5.7e: `exp / tanh` correlation-upper-bound composers -/

/-- **`bridge.bound` from an `exp(-(M·d(0,w)))` correlation upper bound, small
regime** (Step 119 plan Step 5.7e small-`t·r`).

Given the active range and the analytic input
`correlation {0, w} ≤ exp(-(M · d(0, w)))` together with the small-`t·r`
constraint `M · d(0, w) ≤ 1` and `α ≥ 1`, conclude the zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. `pseudoMassG_ge_exp_of_tr_le_one` (small-`t·r`, with `t := M · d(0,w) / r`,
   `t · r = M · d(0,w) ≤ 1`) yields
   `exp(-(M · d(0,w))) ≤ pseudoMassG α r (M · d(0,w) / r)`.
2. Transitivity with the input gives
   `correlation ≤ pseudoMassG α r (M · d(0,w) / r)`.
3. `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG` (#3173)
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (w : Fin d → ℤ)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ)))) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  set t : ℝ := M * (latticeDistance d 0 w : ℝ) / r with ht_def
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have ht_nn : 0 ≤ t := by
    apply div_nonneg
    · exact mul_nonneg hM hdist_nn
    · exact hr.le
  have htr_eq : t * r = M * (latticeDistance d 0 w : ℝ) := by
    rw [ht_def, div_mul_cancel₀ _ (ne_of_gt hr)]
  have htr_le_one : t * r ≤ 1 := by rw [htr_eq]; exact hsmall
  have hpm_ge_exp : Real.exp (-(t * r)) ≤ pseudoMassG α r t :=
    pseudoMassG_ge_exp_of_tr_le_one hα ht_nn hr htr_le_one
  have hcorr_le_pm : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
      ≤ pseudoMassG α r t := by
    have heq : Real.exp (-(t * r)) = Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
      rw [htr_eq]
    rw [← heq] at h_exp_upper
    exact h_exp_upper.trans hpm_ge_exp
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    hα hr d Λ p hM w hcorr hcorr_le_pm

/-- **`bridge.bound` from an `exp(-(M·d(0,w))) / (M·d(0,w))^α` correlation
upper bound, large regime** (Step 119 plan Step 5.7e large-`t·r`).

Given the active range and the analytic input
`correlation {0, w} ≤ exp(-(M · d(0, w))) / (M · d(0, w))^α` together with the
large-`t·r` constraint `1 ≤ M · d(0, w)` and `α ≥ 1`, conclude the zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. `pseudoMassG_ge_exp_div_pow_of_tr_ge_one` (large-`t·r`, with
   `t := M · d(0,w) / r`, `t · r = M · d(0,w) ≥ 1`) yields
   `exp(-(M · d(0,w))) / (M · d(0,w))^α ≤ pseudoMassG α r (M · d(0,w) / r)`.
2. Transitivity with the input gives
   `correlation ≤ pseudoMassG α r (M · d(0,w) / r)`.
3. `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG` (#3173)
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (w : Fin d → ℤ)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ))
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hMd_nn : 0 ≤ M * (latticeDistance d 0 w : ℝ) := le_trans zero_le_one hlarge
  have hM : 0 ≤ M := by
    by_contra hMneg
    push Not at hMneg
    have : M * (latticeDistance d 0 w : ℝ) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hMneg.le, hdist_nn⟩)
    linarith
  set t : ℝ := M * (latticeDistance d 0 w : ℝ) / r with ht_def
  have ht_nn : 0 ≤ t := div_nonneg hMd_nn hr.le
  have htr_eq : t * r = M * (latticeDistance d 0 w : ℝ) := by
    rw [ht_def, div_mul_cancel₀ _ (ne_of_gt hr)]
  have htr_ge_one : 1 ≤ t * r := by rw [htr_eq]; exact hlarge
  have hpm_ge_exp_div_pow :
      Real.exp (-(t * r)) / (t * r) ^ α ≤ pseudoMassG α r t :=
    pseudoMassG_ge_exp_div_pow_of_tr_ge_one α htr_ge_one
  have hcorr_le_pm : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
      ≤ pseudoMassG α r t := by
    have heq : Real.exp (-(t * r)) / (t * r) ^ α =
        Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
          (M * (latticeDistance d 0 w : ℝ)) ^ α := by
      rw [htr_eq]
    rw [← heq] at h_exp_upper
    exact h_exp_upper.trans hpm_ge_exp_div_pow
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_pseudoMassG
    hα hr d Λ p hM w hcorr hcorr_le_pm

/-- **`bridge.bound` from a `tanh(βJ)^d(0,w)` correlation upper bound, small
regime** (Step 119 plan Step 5.7e tanh-input small-`t·r`).

Given:

- `0 ≤ β·J` (ferromagnetic phase / nonneg coupling);
- `M ≤ highTempExpRate β J = -log(tanh(β·J))`;
- `0 ≤ M` and the small-distance constraint `M · d(0,w) ≤ 1`;
- the active range for the correlation;
- the cubic-path tanh-decay upper bound
  `correlation {0, w} ≤ tanh(β·J)^(latticeDistance d 0 w)`,

conclude the zero-anchored `bridge.bound` shape
`M · d(0, w) ≤ pseudoMassFromParamsAtPair 0 w · r`.

Proof chain:
1. Step 5.7d `tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate`
   with `r := 1` yields `tanh(β·J)^k ≤ exp(-(M · k))` for every `k : ℕ`
   (using `M · 1 = M ≤ highTempExpRate β J`).
2. Transitivity gives `correlation ≤ exp(-(M · d(0,w)))`.
3. The small-regime composer
   `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg`
   produces the bridge-shape conclusion. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {M : ℝ} (hM : 0 ≤ M) (hMrate : M ≤ highTempExpRate β J)
    (w : Fin d → ℤ)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_tanh_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hMrate_one : M * (1 : ℝ) ≤ highTempExpRate β J := by
    rw [mul_one]; exact hMrate
  have h_tanh_le_exp :
      Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w ≤
        Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) :=
    tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate hβJ hMrate_one _
  have h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ))) := by
    have h := h_tanh_upper.trans h_tanh_le_exp
    have heq : Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) =
        Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ))) := by
      rw [mul_one]
    rw [heq] at h
    exact h
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d Λ p hM w hsmall hcorr h_exp_upper

/-! ## Step 119 plan Step 5.7f: `hbase` quantifier composers -/

/-- **`hbase` quantifier composer via small/large trichotomy on `M · d(0, w)`**
(Step 119 plan Step 5.7f).

Given `0 ≤ M` and per-nonzero-`w` analytic-input families for both regimes of
`M · d(0, w)`, the trichotomy dispatches each `w ≠ 0` to either the
small-regime composer
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg` or the
large-regime composer
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`,
producing the universally-quantified shape required by the `hbase` field of
`PseudoMassLatticeDistanceBridge_of_cubicTanh_family` (#3172).

The two analytic-input families:
- `h_corr_small`: for each `w ≠ 0` with `M · d(0, w) ≤ 1`,
  `correlation {0, w} ≤ exp(-(M · d(0, w)))`.
- `h_corr_large`: for each `w ≠ 0` with `1 ≤ M · d(0, w)`,
  `correlation {0, w} ≤ exp(-(M · d(0, w))) / (M · d(0, w))^α`.

The trichotomy is by `le_or_lt (M · d(0, w)) 1`: if `≤ 1`, apply the
small-regime composer; otherwise `1 < M · d(0, w)` ⇒ `1 ≤ M · d(0, w)`, apply
the large-regime composer. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))))
    (h_corr_large : ∀ w : Fin d → ℤ, w ≠ 0 →
      1 ≤ M * (latticeDistance d 0 w : ℝ) →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  intro w hw_ne
  by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
  · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
      hα hr d Λ p hM w hsmall (h_corr_active w hw_ne)
      (h_corr_small w hw_ne hsmall)
  · push Not at hsmall
    have hlarge_le : 1 ≤ M * (latticeDistance d 0 w : ℝ) := hsmall.le
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
      hα hr d Λ p w hlarge_le (h_corr_active w hw_ne)
      (h_corr_large w hw_ne hlarge_le)

/-- **`hbase` quantifier composer from a uniform `exp(-(M·d))/max(1, M·d)^α`
correlation upper bound** (Step 119 plan Step 5.7f, unified-input variant).

Convenience wrapper for
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy` taking a
single uniform correlation upper bound in the unified form
`correlation {0, w} ≤ exp(-(M · d(0, w))) / max 1 (M · d(0, w))^α`,
which is automatically both:
- ≤ `exp(-(M · d(0, w)))` in the small regime (where `max 1 (M·d) = 1`,
  hence the denominator is 1);
- ≤ `exp(-(M · d(0, w))) / (M · d(0, w))^α` in the large regime (where
  `max 1 (M·d) = M·d`).

Useful when the caller has a single uniform-shape bound, e.g., a Simon-Lieb
exponential decay augmented with polynomial correction. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_max_pow
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_upper : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            max 1 (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  apply pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_trichotomy
    hα hr d Λ p hM h_corr_active
  · intro w hw_ne hsmall
    have hbound := h_corr_upper w hw_ne
    have hmax_eq : max (1 : ℝ) (M * (latticeDistance d 0 w : ℝ)) = 1 :=
      max_eq_left hsmall
    rw [hmax_eq, one_pow, div_one] at hbound
    exact hbound
  · intro w hw_ne hlarge
    have hbound := h_corr_upper w hw_ne
    have hmax_eq : max (1 : ℝ) (M * (latticeDistance d 0 w : ℝ)) =
        M * (latticeDistance d 0 w : ℝ) :=
      max_eq_right hlarge
    rw [hmax_eq] at hbound
    exact hbound

/-! ## Step 119 plan Step 5.7i: tanh + exp/pow combined hbase composer -/

/-- **`hbase` quantifier composer with asymmetric tanh / exp inputs**
(Step 119 plan Step 5.7i).

Takes the small-regime analytic input in `tanh(β·J)^d(0,w)` form (the natural
output of cubic-path tanh decay infrastructure) and the large-regime input
in `exp(-(M·d))/(M·d)^α` form, dispatching by case-split on
`M · d(0,w) ≤ 1`.

In the small regime, applies Step 5.7e tanh-input variant
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg`
(PR #3176), which internally uses Step 5.7d (PR #3175) to convert tanh form
to exp form. In the large regime, applies Step 5.7e large-input variant
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`
directly.

This asymmetric composer matches the natural shape of analytic inputs
arising from GJ §17.5 derivations: tanh-typed small-regime cubic-path
estimates combined with exp/polynomial-typed large-regime decay. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_exp_trichotomy
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {M : ℝ} (hM : 0 ≤ M) (hMrate : M ≤ highTempExpRate β J)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_tanh_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w)
    (h_corr_exp_large : ∀ w : Fin d → ℤ, w ≠ 0 →
      1 ≤ M * (latticeDistance d 0 w : ℝ) →
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
            (M * (latticeDistance d 0 w : ℝ)) ^ α) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  intro w hw_ne
  by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
  · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_tanh_pow_smallReg
      hα hr d Λ p hβJ hM hMrate w hsmall (h_corr_active w hw_ne)
      (h_corr_tanh_small w hw_ne hsmall)
  · push Not at hsmall
    have hlarge_le : 1 ≤ M * (latticeDistance d 0 w : ℝ) := hsmall.le
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
      hα hr d Λ p w hlarge_le (h_corr_active w hw_ne)
      (h_corr_exp_large w hw_ne hlarge_le)

/-! ## Step 119 plan Step 5.7j: Simon-Lieb dist ≥ 2 direct bridge.bound -/

/-- **Simon-Lieb dist ≥ 2 direct `bridge.bound` composer in the
small-`M·d` regime** (Step 119 plan Step 5.7j).

Combines Step 5.7h (PR #3179)'s `correlationInfinite ≤
exp(-(simonLiebRate/2 · dist))` for `dist ≥ 2` with Step 5.7e small-regime
(PR #3176) for `M · d(0,w) ≤ 1`, yielding the per-`w` zero-anchored
`bridge.bound` shape `M · d(0, w) ≤ pseudoMass · r` directly from
Simon-Lieb infrastructure.

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d)`, `β·J·(2d) ≤ 1` for the Simon-Lieb exp-form
  bound from Step 5.7g/h.
- `0 ≤ M` and `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `M · d(0, w) ≤ 1` for the small-`t·r` regime of pseudoMassG.
- `2 ≤ latticeDistance d 0 w` to exclude the adjacent `dist = 1` case.
- Active range `correlationInfinite ∈ Ioo 0 2` at `{0, w}`.

The adjacent `dist = 1` and large-`M·d` regimes require separate inputs. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have h_simonLieb :=
    correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
      hβJ hβJd_pos hβJd_le hdist (i := 0) (j := w)
  have hdist_nn : (0 : ℝ) ≤ (latticeDistance d 0 w : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
    refine h_simonLieb.trans ?_
    apply Real.exp_le_exp.mpr
    have hrate_mul : -(simonLiebRate β J d / 2) * (latticeDistance d 0 w : ℝ) ≤
        -(M * (latticeDistance d 0 w : ℝ)) := by
      have hmono : M ≤ simonLiebRate β J d / 2 := hMrate
      nlinarith [hdist_nn, hmono]
    exact hrate_mul
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) hM w hsmall hcorr h_exp_upper

/-! ## Step 119 plan Step 5.7j-large: Simon-Lieb large-regime bridge.bound -/

/-- **Polynomial absorption into an exponential rate gap**.

If `1 ≤ t`, then the polynomial factor `t^α` is bounded by `exp(α * t)`.
This is the elementary analytic estimate used to convert a stronger
Simon-Lieb exponential rate into the large-regime
`exp(-(M*d))/(M*d)^α` input expected by `pseudoMassG`. -/
private theorem pow_le_exp_nat_mul_self_of_one_le
    (α : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    t ^ α ≤ Real.exp ((α : ℝ) * t) := by
  have ht_pos : 0 < t := zero_lt_one.trans_le ht
  rw [← Real.exp_log (pow_pos ht_pos α)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  have hlog_le_t : Real.log t ≤ t := by
    have hlog_le_sub := Real.log_le_sub_one_of_pos ht_pos
    linarith
  exact mul_le_mul_of_nonneg_left hlog_le_t (by positivity)

/-- **Large-regime Simon-Lieb exponential-to-polynomial input**.

For `dist ≥ 2`, Simon-Lieb gives
`correlation ≤ exp(-(simonLiebRate/2) * dist)`. If `M` is small enough that
`((α:ℝ)+1) * M ≤ simonLiebRate/2`, then on the large regime
`1 ≤ M * dist` the polynomial denominator `(M*dist)^α` is absorbed by the
exponential rate gap, yielding the exact input shape consumed by
`pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg`. -/
theorem correlationInfinite_latticeGraph_le_exp_neg_M_dist_div_pow_of_simonLieb_largeReg
    {α d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ)) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
      ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) /
          (M * (latticeDistance d 0 w : ℝ)) ^ α := by
  let R : ℝ := simonLiebRate β J d / 2
  let D : ℝ := (latticeDistance d 0 w : ℝ)
  let T : ℝ := M * D
  have h_simonLieb :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(R * D)) := by
    simpa [R, D] using
      correlationInfinite_latticeGraph_le_exp_neg_half_simonLiebRate_dist_of_dist_ge_two
        hβJ hβJd_pos hβJd_le hdist (i := 0) (j := w)
  have hD_nn : 0 ≤ D := by
    dsimp [D]
    exact_mod_cast Nat.zero_le _
  have hT_large : 1 ≤ T := by simpa [T, D] using hlarge
  have hT_pos : 0 < T := zero_lt_one.trans_le hT_large
  have hT_pow_pos : 0 < T ^ α := pow_pos hT_pos α
  have hcoef : (α : ℝ) * M ≤ R - M := by
    change (α : ℝ) * M ≤ simonLiebRate β J d / 2 - M
    linarith
  have hgap_arg : (α : ℝ) * T ≤ (R - M) * D := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hD_nn
    nlinarith [hmul]
  have hpoly_gap : T ^ α ≤ Real.exp ((R - M) * D) :=
    (pow_le_exp_nat_mul_self_of_one_le α hT_large).trans
      (Real.exp_le_exp.mpr hgap_arg)
  have hmul_gap :
      Real.exp (-(R * D)) * T ^ α ≤ Real.exp (-(M * D)) := by
    calc
      Real.exp (-(R * D)) * T ^ α
          ≤ Real.exp (-(R * D)) * Real.exp ((R - M) * D) :=
            mul_le_mul_of_nonneg_left hpoly_gap (Real.exp_nonneg _)
      _ = Real.exp (-(M * D)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have h_exp_div :
      Real.exp (-(R * D)) ≤ Real.exp (-(M * D)) / T ^ α := by
    exact (le_div_iff₀ hT_pow_pos).mpr hmul_gap
  exact h_simonLieb.trans (by simpa [T, D] using h_exp_div)

/-- **Simon-Lieb dist ≥ 2 direct `bridge.bound` composer in the
large-`M·d` regime**.

This removes the earlier small-regime-only bottleneck for non-adjacent pairs:
when `1 ≤ M · d(0,w)` and `M` is small enough relative to the Simon-Lieb rate,
the polynomial denominator required by the large-regime `pseudoMassG` lower
bound is absorbed by the exponential rate gap. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_largeReg
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hdist : 2 ≤ latticeDistance d 0 w)
    (hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ))
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have h_exp_large :=
    correlationInfinite_latticeGraph_le_exp_neg_M_dist_div_pow_of_simonLieb_largeReg
      (α := α) hβJ hβJd_pos hβJd_le hMrate hdist hlarge
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_div_pow_largeReg
    hα hr d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) w hlarge hcorr h_exp_large

/-! ## Step 119 plan Step 5.7k: adjacent dist = 1 specialization -/

/-- **Adjacent (`dist = 1`) `bridge.bound` composer in the small-`M` regime**
(Step 119 plan Step 5.7k).

Specialization of `pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg`
(PR #3176) to `latticeDistance d 0 w = 1`. With `M ≤ 1`, the small-regime
constraint `M · d(0, w) ≤ 1` is automatic, and the bound shape collapses to
`M ≤ pseudoMass · r`.

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ M`, `M ≤ 1`.
- `latticeDistance d 0 w = 1` (adjacent pair).
- Active range `correlationInfinite ∈ Ioo 0 2`.
- Adjacent exp bound `correlationInfinite ≤ exp(-M)`.

Conclusion: `M ≤ pseudoMass · r`. Used to close the adjacent slot of a
full `dist ≥ 1` `hbase` quantifier, complementing Step 5.7j (PR #3181)'s
`dist ≥ 2` Simon-Lieb composer. -/
theorem pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {M : ℝ} (hM : 0 ≤ M) (hM_le_one : M ≤ 1)
    {w : Fin d → ℤ} (hdist : latticeDistance d 0 w = 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_exp_upper :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-M)) :
    M ≤ pseudoMassFromParamsAtPair hα hr d Λ p 0 w * r := by
  have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
    rw [hdist]; norm_cast
  have hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1 := by
    rw [hdist_cast, mul_one]; exact hM_le_one
  have h_exp_upper' :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {0, w}
        ≤ Real.exp (-(M * (latticeDistance d 0 w : ℝ))) := by
    rw [hdist_cast, mul_one]; exact h_exp_upper
  have h := pseudoMassFromParamsAtPair_M_dist_zero_le_of_corr_le_exp_smallReg
    hα hr d Λ p hM w hsmall hcorr h_exp_upper'
  rw [hdist_cast, mul_one] at h
  exact h

/-! ## Step 119 plan Step 5.7l: combined hbase composer (Simon-Lieb + adjacent) -/

/-- **Combined small-regime `bridge.bound` composer for `dist ≥ 1`**
(Step 119 plan Step 5.7l).

Per-`w` composer dispatching by `latticeDistance d 0 w = 1` (adjacent)
vs `≥ 2`:
- adjacent: Step 5.7k (PR #3182).
- non-adjacent: Step 5.7j (PR #3181, Simon-Lieb direct).

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d)`, `β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ 1`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `M · d(0, w) ≤ 1` (small-`t·r` regime).
- Active range `correlation {0, w} ∈ Ioo 0 2`.
- Per-pair `correlation`-upper-bound family:
  - adjacent: `correlation {0, w} ≤ exp(-M)` at `dist = 1`.
  - non-adjacent: implicit via Simon-Lieb #3179 / #3181.

Conclusion: `M · d(0, w) ≤ pseudoMass · r`.

This completes the per-`w` `bridge.bound` API for `dist ≥ 1` in the
small-`M` regime, with Simon-Lieb supplying the non-adjacent exp form
and a separately-provided adjacent input. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0)
    (hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have hdist_pos : 0 < latticeDistance d 0 w := by
    apply Nat.pos_of_ne_zero
    intro h_eq_zero
    exact hw_ne ((IsingModel.latticeDistance_eq_zero_iff d 0 w).mp h_eq_zero).symm
  by_cases h_eq_one : latticeDistance d 0 w = 1
  · have h_adj_bound : Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
          ≤ Real.exp (-M) := h_adj_exp h_eq_one
    have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
      rw [h_eq_one]; norm_cast
    have hM_le_one : M ≤ 1 := by
      have := hsmall
      rw [hdist_cast, mul_one] at this
      exact this
    have h := pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
      hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hM hM_le_one h_eq_one hcorr h_adj_bound
    rw [hdist_cast, mul_one]
    exact h
  · have h_ge_two : 2 ≤ latticeDistance d 0 w := by omega
    exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
      hα hr d hβJ hβJd_pos hβJd_le hM hMrate h_ge_two hsmall hcorr

/-! ## Step 119 plan Step 5.7m: ∀ w ≠ 0 hbase quantifier composer -/

/-- **`hbase` quantifier composer from Step 5.7l per-`w` composer**
(Step 119 plan Step 5.7m).

Lifts `pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined`
(Step 5.7l, PR #3183) to the universally-quantified
`∀ w ≠ 0, M · d(0, w) ≤ pseudoMass · r` shape, the zero-anchored input
required by `pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`
(existing).

Hypotheses (per `w ≠ 0` and uniform):
- `1 ≤ α`, `0 < r` (pseudoMass parameters).
- `0 ≤ β·J`, `0 < β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `h_corr_active`: per-`w ≠ 0` active range.
- `h_corr_small`: per-`w ≠ 0`, `M · d(0, w) ≤ 1` (small-`t·r` regime).
  Restrictive — for arbitrary `w` forces `M = 0` unless bounded support.
- `h_adj_exp`: per-`w` with `dist(0, w) = 1`, `correlation ≤ exp(-M)`.

Conclusion: `∀ w ≠ 0, M · d(0, w) ≤ pseudoMass · r`. Suitable input for
`pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored` lifting to all
distinct pairs. -/
theorem pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  intro w hw_ne
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_smallReg_combined
    hα hr d hβJ hβJd_pos hβJd_le hM hMrate hw_ne
    (h_corr_small w hw_ne) (h_corr_active w hw_ne)
    (h_adj_exp w)

/-! ## Step 119 plan Step 5.7n: all-pair bound lift from Step 5.7m -/

/-- **All-pair `bridge.bound` from Step 5.7m via the translation lift**
(Step 119 plan Step 5.7n).

Composes Step 5.7m (`...zero_anchored_simonLieb_smallReg_uniform`, PR #3184)
with the existing `pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`
to produce the all-pair shape
`∀ x z, x ≠ z → M · d(x, z) ≤ pseudoMass · r`, matching the `bound` field
signature of `PseudoMassLatticeDistanceBridge`.

Hypotheses (uniform per `w ≠ 0`; only `bound` is lifted to all pairs here —
active range remains the zero-anchored input consumed by Step 5.7m):
- `1 ≤ α`, `0 < r`, `0 ≤ J`, `0 < β` (pseudoMass / ferromagnetic).
- `0 < β·J·(2d) ≤ 1` for Simon-Lieb.
- `0 ≤ M`, `M ≤ simonLiebRate β J d / 2` for rate-domination.
- `h_corr_active`: per-`w ≠ 0` active range at `{0, w}`.
- `h_corr_small`: per-`w ≠ 0`, `M · d(0, w) ≤ 1`.
- `h_adj_exp`: per-`w` with `dist(0, w) = 1`, `correlation ≤ exp(-M)`.

This is the final structural step in the Step 5.7 plumbing chain. -/
theorem pseudoMassFromParamsAtPair_all_pair_simonLieb_smallReg_bound
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have h_zero_anchored :=
    pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform
      hα hr d hβJ hβJd_pos hβJd_le hM hMrate
      h_corr_active h_corr_small h_adj_exp
  exact pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ h_zero_anchored

/-! ## Step 119 plan Step 5.7j-large: full Simon-Lieb trichotomy composer -/

/-- **Combined Simon-Lieb `bridge.bound` composer by adjacent/small/large cases**.

For a single nonzero anchored displacement `w`, this removes the impossible
uniform small-regime assumption by splitting into:

- `dist(0,w) = 1`: use the adjacent input;
- `2 ≤ dist(0,w)` and `M * dist(0,w) ≤ 1`: use the Simon-Lieb small-regime
  composer;
- `2 ≤ dist(0,w)` and `1 ≤ M * dist(0,w)`: use the Simon-Lieb large-regime
  rate-gap composer.

The rate condition `((α:ℝ)+1) * M ≤ simonLiebRate β J d / 2` is stronger than
the small-regime domination `M ≤ simonLiebRate β J d / 2`, so it feeds both
non-adjacent branches. -/
theorem pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
              ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    M * (latticeDistance d 0 w : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  have hMrate_small : M ≤ simonLiebRate β J d / 2 := by
    have hfactor : (1 : ℝ) ≤ (α : ℝ) + 1 := by
      exact le_add_of_nonneg_left (Nat.cast_nonneg α)
    have hM_le_scaled : M ≤ ((α : ℝ) + 1) * M := by
      nlinarith [hfactor, hM_pos.le]
    exact hM_le_scaled.trans hMrate
  have hdist_pos : 0 < latticeDistance d 0 w := by
    apply Nat.pos_of_ne_zero
    intro h_eq_zero
    exact hw_ne ((IsingModel.latticeDistance_eq_zero_iff d 0 w).mp h_eq_zero).symm
  by_cases h_eq_one : latticeDistance d 0 w = 1
  · have hdist_cast : (latticeDistance d 0 w : ℝ) = 1 := by
      rw [h_eq_one]; norm_cast
    have h := pseudoMassFromParamsAtPair_zero_le_of_corr_le_exp_adjacent
      hα hr d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hM_pos.le hM_le_one h_eq_one hcorr
      (h_adj_exp h_eq_one)
    rw [hdist_cast, mul_one]
    exact h
  · have h_ge_two : 2 ≤ latticeDistance d 0 w := by omega
    by_cases hsmall : M * (latticeDistance d 0 w : ℝ) ≤ 1
    · exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_smallReg
        hα hr d hβJ hβJd_pos hβJd_le hM_pos.le hMrate_small
        h_ge_two hsmall hcorr
    · have hlarge : 1 ≤ M * (latticeDistance d 0 w : ℝ) :=
        (lt_of_not_ge hsmall).le
      exact pseudoMassFromParamsAtPair_M_dist_zero_le_of_simonLieb_largeReg
        hα hr d hβJ hβJd_pos hβJd_le hMrate h_ge_two hlarge hcorr

/-- **Uniform zero-anchored bound from the full Simon-Lieb trichotomy**.

This is the replacement for
`pseudoMassFromParamsAtPair_zero_anchored_simonLieb_smallReg_uniform` when
`M > 0`: it no longer assumes `∀ w ≠ 0, M * dist(0,w) ≤ 1`. -/
theorem pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) 0 w * r := by
  intro w hw_ne
  exact pseudoMassFromParamsAtPair_M_dist_zero_le_simonLieb_trichotomy_combined
    hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_le_one hMrate hw_ne
    (h_corr_active w hw_ne) (h_adj_exp w)

/-- **All-pair bound from the full Simon-Lieb trichotomy**.

Composes the uniform zero-anchored trichotomy with the translation lift
`pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored`, producing the
`PseudoMassLatticeDistanceBridge.bound` field without the globally impossible
small-regime hypothesis. -/
theorem pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_corr_active : ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have h_zero_anchored :=
    pseudoMassFromParamsAtPair_zero_anchored_simonLieb_trichotomy_uniform
      hα hr d hβJ hβJd_pos hβJd_le hM_pos hM_le_one hMrate
      h_corr_active h_adj_exp
  exact pseudoMassFromParamsAtPair_lower_bound_of_zero_anchored
    hα hr d hJ hβ h_zero_anchored

/-! ## Step 119 plan Step 5.7o: active range from tanh-power lower bound -/

/-- **All-pair active range from `0 < β·J`** (Step 119 plan Step 5.7o).

Direct provider of the `active` field of `PseudoMassLatticeDistanceBridge`:
given `0 < β·J` (strict positivity), `tanh(β·J) > 0`, so
`tanh(β·J)^d(x,z) > 0` for every distinct pair `(x, z)`, and combined with
the existing tanh-power lower bound `tanh(β·J)^d(0, r) ≤ twoPointFunction d r`
(`PathLowerBound.twoPointFunction_ge_tanh_betaJ_pow_dist`) plus translation
invariance and the universal upper bound
`correlationInfinite_latticeGraph_le_one`, yields
`correlationInfinite ∈ Ioo 0 2` for every distinct pair.

Complements Step 5.7n (PR #3185)'s all-pair bound provider, completing the
structural input set for building a concrete `PseudoMassLatticeDistanceBridge`
value directly from concrete analytic inputs (without going through the
vacuous `cubicTanhProfileBound` family). -/
theorem correlationInfinite_pair_active_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  have hJ : 0 ≤ J := by
    have hJ_pos : 0 < J := (mul_pos_iff_of_pos_left hβ).mp hβJ_pos
    exact hJ_pos.le
  intro x z hxz
  refine ⟨?_, ?_⟩
  · -- Lower bound: 0 < tanh(β·J)^d(x,z) ≤ correlation
    have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
    have htanh_pos : 0 < Real.tanh (β * J) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
    have hpow_pos : 0 < Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 (z - x) :=
      pow_pos htanh_pos _
    have h_tanh_le_two_pt :=
      twoPointFunction_ge_tanh_betaJ_pow_dist (d := d) (J := J) (β := β)
        hJ hβ hzx_ne
    have htrans :
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
          = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (z - x) := by
      rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
      exact twoPointFunction_apply d _ (z - x)
    rw [htrans]
    exact lt_of_lt_of_le hpow_pos h_tanh_le_two_pt
  · -- Upper bound: correlation ≤ 1 < 2
    have h_le_one := correlationInfinite_latticeGraph_le_one d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
    linarith

/-! ## Step 119 plan Step 5.7p: direct PseudoMassLatticeDistanceBridge constructor -/

/-- **Direct `PseudoMassLatticeDistanceBridge` constructor from bound + active
providers** (Step 119 plan Step 5.7p).

Convenience structural constructor taking:
- `M_inf : ℝ`, `M_inf_pos : 0 < M_inf` (the rate);
- `hf : Ferromagnetic ⟨J, 0, β⟩`;
- `bound`: the all-pair shape from Step 5.7n (PR #3185);
- `active`: the all-pair shape from Step 5.7o (PR #3186);

and producing a `PseudoMassLatticeDistanceBridge` value directly. This is
the alternative constructor matching the natural shape of the Step 5.7n /
Step 5.7o providers, bypassing the (vacuous) `cubicTanhProfileBound`
family path. -/
def PseudoMassLatticeDistanceBridge_of_bound_active
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    {M_inf : ℝ} (M_inf_pos : 0 < M_inf)
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (bound : ∀ x z : Fin d → ℤ, x ≠ z →
      M_inf * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r)
    (active : ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2) :
    PseudoMassLatticeDistanceBridge hα hr d J β where
  M_inf := M_inf
  M_inf_pos := M_inf_pos
  hf := hf
  bound := bound
  active := active

end Ambient
end IsingModel
