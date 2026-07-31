import IsingModel.PseudoMass.HLSCorrelationCapstone
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMassTanhProfileCubicPair
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.PolyDecay

/-!
# Conditional PseudoMassLatticeDistanceBridge constructor: core translation reductions

Core (Step 119 plan Step 5.7) building blocks for the conditional
`PseudoMassLatticeDistanceBridge` constructor: the translation reductions of the
pair correlation, `pseudoMassFromParamsAtPair`, and lattice distance, the
zero-anchored bound lift, the `cubicTanhProfileBound`-family active-range lift,
the family-based bridge constructor, and the `pseudoMassG`-shaped atomic
reductions.

This is a structural child of `HLSBridgeFromCubicTanh.lean`; see that umbrella
module for the full overview.

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

/-- **Bound lift from the zero-anchored uniform pseudo-mass lower bound**
(Step 119 plan Step 5.7).

If for every nonzero displacement `w` the zero-anchored pseudo-mass dominates
`M_inf · d(0, w)`, then for every distinct pair `(x, z)` the pair pseudo-mass
dominates `M_inf · d(x, z)`. Direct consequence of the translation reductions
`pseudoMassFromParamsAtPair_eq_displacement` and
`latticeDistance_translate_eq` at `w = z - x`. -/
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
    exact_mod_cast latticeDistance_translate_eq d x z
  have h_pseudo := pseudoMassFromParamsAtPair_eq_displacement hα hr d hJ hβ x z
  rw [h_dist, h_pseudo]
  exact hbase (z - x) hzx_ne

/-- **Active-range lift from a uniform `cubicTanhProfileBound` family**
(Step 119 plan Step 5.7).

If a `cubicTanhProfileBound` holds at every nonzero displacement, then the
pair correlation lies in the active range `Ioo 0 2` for every distinct pair
`(x, z)`.  This is a conditional compatibility wrapper; in positive dimension,
with `0 < r`, `0 < β * J`, and `β * J * (2 * d) < 1`,
`CubicPseudoMassTanhProfileNoGo` shows that the all-displacement family itself
is impossible. -/
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
a route for producing an input-free positive-dimensional high-temperature
bridge; use the direct Simon-Lieb trichotomy constructors for the corresponding
adjacent/bound/active-provider shape.

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

end Ambient
end IsingModel
