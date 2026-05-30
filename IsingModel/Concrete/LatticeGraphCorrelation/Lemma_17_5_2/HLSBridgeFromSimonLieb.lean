import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# Bridge-to-HLS sum bundle: Simon-Lieb + adjacent + ferromagnetic chain

Bundled GJ-proposition-size PR consolidating the structural chain from
Simon-Lieb / adjacent / ferromagnetic concrete analytic inputs to the HLS
sum bound `tsum_correlationInfinite_pair_product_le_HLS_const` (#3171).

Built on the atomic Step 5.7d-p building blocks (#3175-#3187):

- Step 5.7d/e (#3175/#3176): per-`w` exp/tanh → `bridge.bound` composers
- Step 5.7f/i (#3177/#3180): trichotomy `hbase` quantifier composers
- Step 5.7g/h (#3178/#3179): Simon-Lieb exp-form correlation bounds
- Step 5.7j-l (#3181-#3183): combined Simon-Lieb + adjacent per-`w` composers
- Step 5.7m/n (#3184/#3185): per-`w` to ∀ `w` ≠ 0 to all-pair lifts
- Step 5.7o (#3186): active range from `0 < β·J`
- Step 5.7p (#3187): direct `PseudoMassLatticeDistanceBridge` constructor

This file provides:

1. End-to-end `PseudoMassLatticeDistanceBridge` construction from Simon-Lieb
   + adjacent + ferromagnetic concrete inputs.
2. HLS sum existential consumers at common anchor patterns.
3. Constant-form (explicit `K`) HLS sum consumers.
4. Per-pair specializations for downstream Lemma 17.5.2 finite-stage and
   sandwich machinery.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## End-to-end Simon-Lieb bridge constructor -/

/-- **End-to-end `PseudoMassLatticeDistanceBridge` from Simon-Lieb + adjacent
+ ferromagnetic concrete inputs**.

Combines Step 5.7n (all-pair bound, #3185), Step 5.7o (active range, #3186),
and Step 5.7p (direct constructor, #3187) into a single end-to-end
production of a `PseudoMassLatticeDistanceBridge` value.

Hypotheses:
- `1 ≤ α`, `0 < r` (pseudoMass parameters);
- `0 ≤ J`, `0 < β`, `0 < β · J` (ferromagnetic with strict coupling);
- `0 < β·J·(2d) ≤ 1` (strict high-temperature for Simon-Lieb);
- `0 < M` with `M ≤ simonLiebRate β J d / 2` (rate-dominated);
- `h_corr_small`: per-`w ≠ 0`, `M · d(0, w) ≤ 1`;
- `h_adj_exp`: per-`w` with `dist(0, w) = 1`,
  `correlation ≤ exp(-M)`. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  let h_active :=
    correlationInfinite_pair_active_of_betaJ_pos (d := d) hβ hβJ_pos
  PseudoMassLatticeDistanceBridge_of_bound_active hα hr d hM_pos
    ⟨hJ, le_refl 0, hβ⟩
    (pseudoMassFromParamsAtPair_all_pair_simonLieb_smallReg_bound
      hα hr d hJ hβ hβJd_pos hβJd_le hM_pos.le hMrate
      (fun w hw_ne => h_active 0 w (by intro h; exact hw_ne h.symm))
      h_corr_small h_adj_exp)
    h_active

/-! ## HLS sum existential consumers -/

/-- **HLS sum existential at `(x₀, y₀)` from Simon-Lieb bridge**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_HLS_const hα hr d hαd J β
    (PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
      h_corr_small h_adj_exp)
    x₀ y₀

/-- **HLS sum at the zero anchor `(0, 0)`**. Specialization for the
diagonal x₀ = y₀ = 0 case, the most common form in subsequent derivations. -/
theorem tsum_correlationInfinite_pair_product_zero_anchor_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp 0 0

/-! ## Bridge field providers (summary wrappers) -/

/-- **Summary: all-pair bound provider from Simon-Lieb + adjacent inputs**.

Symmetric wrapper exposing the `bound` field constructor as a standalone
provider, without going through the bridge. Useful for consumers that
need the bound shape separately. -/
theorem all_pair_bound_of_simonLieb_smallReg_adjacent_provider
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
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
  have h_active :=
    correlationInfinite_pair_active_of_betaJ_pos (d := d) hβ hβJ_pos
  exact pseudoMassFromParamsAtPair_all_pair_simonLieb_smallReg_bound
    hα hr d hJ hβ hβJd_pos hβJd_le hM_pos.le hMrate
    (fun w hw_ne => h_active 0 w (by intro h; exact hw_ne h.symm))
    h_corr_small h_adj_exp

/-- **Summary: all-pair active range provider from `0 < β·J`**.

Alias for Step 5.7o (`correlationInfinite_pair_active_of_betaJ_pos`,
PR #3186), exposed in this consumer-facing API file for documentation
completeness alongside the bound provider. -/
theorem all_pair_active_of_betaJ_pos_provider
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
  correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos

/-! ## Tanh-input variants -/

/-- **End-to-end bridge constructor from tanh-power adjacent input**.

Variant of `PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent`
taking the adjacent input in the natural `tanh(β·J)^(d(0,w))` form (= `tanh`
at `dist = 1`) and converting via Step 5.7d (`tanh^d ≤ exp(-(M·d))` from
PR #3175 at `r := 1` with `M ≤ highTempExpRate β J`). -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate_sl : M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate_sl
    h_corr_small
    (fun w hw_eq_one => by
      have hbase := h_adj_tanh w hw_eq_one
      have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
      have hMrate_one : M * (1 : ℝ) ≤ highTempExpRate β J := by
        rw [mul_one]; exact hMrate_htep
      have h_tanh_le_exp :
          Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w ≤
            Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) :=
        tanh_pow_le_exp_neg_M_dist_r_of_M_r_le_highTempExpRate
          hβJ hMrate_one _
      have h_dist_eq : (IsingModel.latticeDistance d 0 w : ℝ) = 1 := by
        rw [hw_eq_one]; norm_cast
      have h_exp_eq :
          Real.exp (-(M * (IsingModel.latticeDistance d 0 w : ℝ) * 1)) =
            Real.exp (-M) := by
        rw [h_dist_eq]; ring_nf
      rw [h_exp_eq] at h_tanh_le_exp
      exact hbase.trans h_tanh_le_exp)

/-- **HLS sum from tanh-power adjacent + Simon-Lieb inputs**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate_sl : M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_HLS_const hα hr d hαd J β
    (PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_tanh_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate_sl hMrate_htep
      h_corr_small h_adj_tanh)
    x₀ y₀

end Ambient
end IsingModel
