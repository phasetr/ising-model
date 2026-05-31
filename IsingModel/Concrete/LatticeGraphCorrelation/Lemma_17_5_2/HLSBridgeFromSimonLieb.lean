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
- Full trichotomy extension (#3373): adjacent/small/large Simon-Lieb bridge
  constructors and canonical entry points without the uniform small-regime
  premise

This file provides:

1. End-to-end `PseudoMassLatticeDistanceBridge` construction from Simon-Lieb
   + adjacent + ferromagnetic concrete inputs, including full trichotomy
   constructors.
2. HLS sum existential consumers at common anchor patterns.
3. Constant-form (explicit `K`) HLS sum consumers.
4. Per-pair specializations for downstream Lemma 17.5.2 finite-stage and
   sandwich machinery.
5. Canonical `canonical_*` entry points formerly housed in the retired
   `HLSBridgeSummary` wrapper module.

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

/-- **End-to-end `PseudoMassLatticeDistanceBridge` from the full Simon-Lieb
trichotomy plus adjacent input**.

Variant of `PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent`
that no longer assumes the impossible uniform small-regime hypothesis
`∀ w ≠ 0, M * dist(0,w) ≤ 1`. Non-adjacent pairs are split per displacement
into the existing Simon-Lieb small-regime composer and the large-regime
rate-gap composer. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  let h_active :=
    correlationInfinite_pair_active_of_betaJ_pos (d := d) hβ hβJ_pos
  PseudoMassLatticeDistanceBridge_of_bound_active hα hr d hM_pos
    ⟨hJ, le_refl 0, hβ⟩
    (pseudoMassFromParamsAtPair_all_pair_simonLieb_trichotomy_bound
      hα hr d hJ hβ hβJd_pos hβJd_le hM_pos hM_le_one hMrate
      (fun w hw_ne => h_active 0 w (by intro h; exact hw_ne h.symm))
      h_adj_exp)
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

/-- **HLS sum existential from the full Simon-Lieb trichotomy bridge**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_trichotomy_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
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
    (PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate
      h_adj_exp)
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

/-- **End-to-end trichotomy bridge from tanh-power adjacent input**.

This is the tanh-input analogue of
`PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent`: it converts
the adjacent tanh-power bound to `exp (-M)` and then uses the full
adjacent/small/large Simon-Lieb trichotomy, so there is no uniform small-regime
assumption. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
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

/-- **HLS sum from tanh-power adjacent input and the full Simon-Lieb
trichotomy bridge**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_trichotomy_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
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
    (PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_tanh_adjacent
      hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
      hMrate_htep h_adj_tanh)
    x₀ y₀

/-! ## Variant bundle: per-pair / symmetric / mixed-anchor specializations -/

/-- **HLS sum existential at the diagonal `(x₀, x₀)`**.

Diagonal specialization of
`tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent`
at `y₀ := x₀`, the most common shape for `χ_∞(x₀)^2`-type estimates. -/
theorem tsum_correlationInfinite_pair_product_diagonal_le_const_of_simonLieb
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
    (x₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp x₀ x₀

/-- **HLS sum existential symmetric in `(x₀, y₀)` ↔ `(y₀, x₀)`**.

Symmetric variant under the swap `x₀ ↔ y₀`. Direct consequence of the
non-symmetric form combined with the commutativity of multiplication —
the underlying constant is the same. -/
theorem tsum_correlationInfinite_pair_product_swap_le_const_of_simonLieb
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
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp y₀ x₀

/-- **Ferromagnetic-unfolded form of `PseudoMassLatticeDistanceBridge`
end-to-end constructor**.

The `Ferromagnetic ⟨J, 0, β⟩` witness `⟨hJ, le_refl 0, hβ⟩` is unfolded
to its explicit components, useful for callers that haven't already
packaged the ferromagnetic predicate. -/
def PseudoMassLatticeDistanceBridge_ferromagnetic_unfolded
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
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp

/-- **Constant K positivity from the existential HLS sum bound**.

Exposes the positive K witness extracted from the existential, useful for
downstream `K > 0`-dependent reasoning. -/
theorem hls_const_pos_of_simonLieb
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
    ∃ K : ℝ, 0 < K :=
  let ⟨K, hK_pos, _⟩ :=
    tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
      hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
      h_corr_small h_adj_exp x₀ y₀
  ⟨K, hK_pos⟩

/-- **Active range provider standalone form for the zero anchor**.

Zero-anchored version of `all_pair_active_of_betaJ_pos_provider`. -/
theorem zero_anchor_active_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  intro w hw_ne
  exact correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos 0 w
    (fun h => hw_ne h.symm)

/-- **Per-`w` non-vanishing of correlation from active range**.

Lower bound `0 < correlationInfinite {0, w}` for `w ≠ 0` distilled from
the active range. Useful when only the strict positivity is needed (not
the full `Ioo 0 2` membership). -/
theorem correlationInfinite_pos_of_betaJ_pos_zero_anchor
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w} :=
  (zero_anchor_active_of_betaJ_pos hβ hβJ_pos w hw_ne).1

/-- **Per-pair non-vanishing of correlation from active range**.

Per-distinct-pair version of
`correlationInfinite_pos_of_betaJ_pos_zero_anchor`. -/
theorem correlationInfinite_pos_of_betaJ_pos_pair
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
  (correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos x z hxz).1

/-- **Per-pair upper bound from active range**.

Upper bound `correlationInfinite {x, z} < 2` distilled from the active
range. (The sharper `≤ 1` follows from
`correlationInfinite_latticeGraph_le_one`.) -/
theorem correlationInfinite_lt_two_of_betaJ_pos_pair
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      < 2 :=
  (correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos x z hxz).2

/-! ## Variant bundle: translation invariance properties -/

/-- **Active range at any translated distinct pair `(x + v, z + v)`**.

Direct application of `correlationInfinite_pair_active_of_betaJ_pos`
to the translated pair `(x + v, z + v)`. The translated pair is also
distinct because addition by `v` is injective. -/
theorem correlationInfinite_pair_active_translation_invariant_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (v : Fin d → ℤ) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {x + v, z + v}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  intro x z hxz
  have hxv_ne : x + v ≠ z + v := by
    intro h; apply hxz
    have := add_right_cancel h
    exact this
  exact correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos
    (x + v) (z + v) hxv_ne

/-- **`bridge.bound` at the translated distinct pair `(x + v, z + v)`**.

Direct application of `all_pair_bound_of_simonLieb_smallReg_adjacent_provider`
to the translated pair `(x + v, z + v)`. The translated pair is also
distinct because addition by `v` is injective. -/
theorem pseudoMassFromParamsAtPair_all_pair_bound_translation_invariant
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
        ≤ Real.exp (-M))
    (v : Fin d → ℤ) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d (x + v) (z + v) : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) (x + v) (z + v) * r := by
  intro x z hxz
  have hxv_ne : x + v ≠ z + v := by
    intro h; apply hxz; exact add_right_cancel h
  exact all_pair_bound_of_simonLieb_smallReg_adjacent_provider
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp (x + v) (z + v) hxv_ne

/-- **HLS sum bound at translated anchor `(x₀ + v, y₀ + v)`**.

Direct application of the HLS sum existential at the translated anchor. -/
theorem tsum_correlationInfinite_pair_product_translated_anchor_le_const_of_simonLieb
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
    (x₀ y₀ v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x₀ + v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {y₀ + v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp (x₀ + v) (y₀ + v)

/-- **HLS sum bound at the displacement anchor `(0, v)`**.

Specialization to the displacement-pair anchor `(0, v)`. -/
theorem tsum_correlationInfinite_pair_product_zero_v_le_const_of_simonLieb
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
    (v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp 0 v

/-- **Lattice-distance displacement identity for the bound shape**.

For distinct `(x, z)`, the bound `M · d(x, z) ≤ pseudoMass · r` rewrites
as `M · d(0, z - x) ≤ pseudoMass · r` using
`latticeDistance_pair_eq_displacement`. -/
theorem bound_shape_displacement_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {M : ℝ} (x z : Fin d → ℤ)
    (hbound : M * (latticeDistance d 0 (z - x) : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 (z - x) * r) :
    M * (latticeDistance d x z : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have h_dist : (latticeDistance d x z : ℝ) =
      (latticeDistance d 0 (z - x) : ℝ) := by
    exact_mod_cast latticeDistance_pair_eq_displacement d x z
  have h_pseudo := pseudoMassFromParamsAtPair_eq_displacement hα hr d hJ hβ x z
  rw [h_dist, h_pseudo]
  exact hbound

/-- **Active range transfer from zero-anchor displacement**.

One-way transfer: if active range holds at the zero-anchored displacement
`(0, z - x)`, then it holds at `(x, z)` by translation invariance of the
pair correlation (`correlationInfinite_pair_eq_displacement`). -/
theorem active_displacement_eq
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (x z : Fin d → ℤ)
    (h_active_zero : Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z - x}
        ∈ Set.Ioo (0 : ℝ) 2) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
  exact h_active_zero

/-- **Composite displacement form for bridge.bound**.

Combining `bound_shape_displacement_eq` and `active_displacement_eq`
factors per-pair `bridge.bound` through the zero-anchored displacement. -/
theorem bridge_bound_active_displacement_composite
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {M : ℝ} (x z : Fin d → ℤ)
    (hbound_zero : M * (latticeDistance d 0 (z - x) : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 (z - x) * r)
    (h_active_zero : Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z - x}
        ∈ Set.Ioo (0 : ℝ) 2) :
    (M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ∧
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 :=
  ⟨bound_shape_displacement_eq hα hr d hJ hβ x z hbound_zero,
   active_displacement_eq hJ hβ x z h_active_zero⟩

/-- **Antipode form: HLS sum at the antipode anchor `(v, -v)`**.

Specialization at the antipode pair anchor `(v, -v)`. -/
theorem tsum_correlationInfinite_pair_product_antipode_le_const_of_simonLieb
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
    (v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp v (-v)

/-! ## Canonical summary entry points -/

/-- Extracts `0 < β * J` from the strict high-temperature product
`0 < β * J * (2d)`. -/
private theorem betaJ_pos_of_betaJ_two_d_pos {β J : ℝ} {d : ℕ}
    (hβJd_pos : 0 < β * J * (2 * d)) :
    0 < β * J := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  by_contra h
  push Not at h
  have : β * J * (2 * d) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h h2d_nn
  linarith

/-- **Selected Simon-Lieb trichotomy bridge rate**.

This concrete rate is small enough to satisfy both scalar side conditions of
the full adjacent/small/large Simon-Lieb bridge:
`M ≤ 1` and `((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2`. -/
noncomputable def simonLiebTrichotomyBridgeRate (α : ℕ) (β J : ℝ) (d : ℕ) :
    ℝ :=
  min 1 ((simonLiebRate β J d / 2) / ((α : ℝ) + 1))

/-- **The selected Simon-Lieb trichotomy bridge rate is positive** in the
strict high-temperature regime. -/
theorem simonLiebTrichotomyBridgeRate_pos
    {α d : ℕ} {β J : ℝ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebTrichotomyBridgeRate α β J d := by
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt
  have hhalf_pos : 0 < simonLiebRate β J d / 2 := by linarith
  have hden_pos : 0 < (α : ℝ) + 1 := by positivity
  dsimp [simonLiebTrichotomyBridgeRate]
  exact lt_min zero_lt_one (div_pos hhalf_pos hden_pos)

/-- **The selected Simon-Lieb trichotomy bridge rate is at most one**. -/
theorem simonLiebTrichotomyBridgeRate_le_one
    (α : ℕ) (β J : ℝ) (d : ℕ) :
    simonLiebTrichotomyBridgeRate α β J d ≤ 1 := by
  dsimp [simonLiebTrichotomyBridgeRate]
  exact min_le_left _ _

/-- **The selected Simon-Lieb trichotomy bridge rate satisfies the rate-gap
condition** used by the full trichotomy bridge. -/
theorem simonLiebTrichotomyBridgeRate_scaled_le_simonLiebRate_half
    (α : ℕ) (β J : ℝ) (d : ℕ) :
    ((α : ℝ) + 1) * simonLiebTrichotomyBridgeRate α β J d ≤
      simonLiebRate β J d / 2 := by
  have hden_pos : 0 < (α : ℝ) + 1 := by positivity
  have hle :
      simonLiebTrichotomyBridgeRate α β J d ≤
        (simonLiebRate β J d / 2) / ((α : ℝ) + 1) := by
    dsimp [simonLiebTrichotomyBridgeRate]
    exact min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_left hle hden_pos.le
  have hcancel :
      ((α : ℝ) + 1) *
          ((simonLiebRate β J d / 2) / ((α : ℝ) + 1)) =
        simonLiebRate β J d / 2 := by
    rw [mul_div_cancel₀ _ hden_pos.ne']
  exact hmul.trans_eq hcancel

/-- **Selected tanh-compatible Simon-Lieb trichotomy bridge rate**.

This concrete rate is the selected Simon-Lieb trichotomy rate additionally
truncated by `highTempExpRate β J`, so it can be used with the tanh-adjacent
canonical path without a separate `M ≤ highTempExpRate β J` caller witness. -/
noncomputable def simonLiebTanhTrichotomyBridgeRate (α : ℕ) (β J : ℝ) (d : ℕ) :
    ℝ :=
  min (simonLiebTrichotomyBridgeRate α β J d) (highTempExpRate β J)

/-- **The selected tanh-compatible Simon-Lieb trichotomy bridge rate is
positive** in the strict high-temperature regime. -/
theorem simonLiebTanhTrichotomyBridgeRate_pos
    {α d : ℕ} {β J : ℝ}
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1) :
    0 < simonLiebTanhTrichotomyBridgeRate α β J d := by
  have hSL_pos : 0 < simonLiebTrichotomyBridgeRate α β J d :=
    simonLiebTrichotomyBridgeRate_pos hβJd_pos hβJd_lt
  have hβJ_pos : 0 < β * J :=
    betaJ_pos_of_betaJ_two_d_pos (β := β) (J := J) (d := d) hβJd_pos
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
  have hhtep_pos : 0 < highTempExpRate β J := by
    unfold highTempExpRate
    exact neg_pos.mpr (Real.log_neg htanh_pos (Real.tanh_lt_one _))
  dsimp [simonLiebTanhTrichotomyBridgeRate]
  exact lt_min hSL_pos hhtep_pos

/-- **The selected tanh-compatible Simon-Lieb trichotomy bridge rate is at
most one**. -/
theorem simonLiebTanhTrichotomyBridgeRate_le_one
    (α : ℕ) (β J : ℝ) (d : ℕ) :
    simonLiebTanhTrichotomyBridgeRate α β J d ≤ 1 := by
  have hle :
      simonLiebTanhTrichotomyBridgeRate α β J d ≤
        simonLiebTrichotomyBridgeRate α β J d := by
    dsimp [simonLiebTanhTrichotomyBridgeRate]
    exact min_le_left _ _
  exact hle.trans (simonLiebTrichotomyBridgeRate_le_one α β J d)

/-- **The selected tanh-compatible Simon-Lieb trichotomy bridge rate satisfies
the Simon-Lieb rate-gap condition** used by the full trichotomy bridge. -/
theorem simonLiebTanhTrichotomyBridgeRate_scaled_le_simonLiebRate_half
    (α : ℕ) (β J : ℝ) (d : ℕ) :
    ((α : ℝ) + 1) * simonLiebTanhTrichotomyBridgeRate α β J d ≤
      simonLiebRate β J d / 2 := by
  have hden_nonneg : 0 ≤ (α : ℝ) + 1 := by positivity
  have hle :
      simonLiebTanhTrichotomyBridgeRate α β J d ≤
        simonLiebTrichotomyBridgeRate α β J d := by
    dsimp [simonLiebTanhTrichotomyBridgeRate]
    exact min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_left hle hden_nonneg
  exact hmul.trans
    (simonLiebTrichotomyBridgeRate_scaled_le_simonLiebRate_half α β J d)

/-- **The selected tanh-compatible Simon-Lieb trichotomy bridge rate is bounded
by `highTempExpRate`**, enabling the tanh-to-exp conversion. -/
theorem simonLiebTanhTrichotomyBridgeRate_le_highTempExpRate
    (α : ℕ) (β J : ℝ) (d : ℕ) :
    simonLiebTanhTrichotomyBridgeRate α β J d ≤ highTempExpRate β J := by
  dsimp [simonLiebTanhTrichotomyBridgeRate]
  exact min_le_right _ _

/-- **Canonical bridge constructor** (exp-adjacent input form, full trichotomy). -/
def canonical_bridge_from_simonLieb_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  have hβJ_pos := betaJ_pos_of_betaJ_two_d_pos (β := β) (J := J) (d := d) hβJd_pos
  PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
    hα hr d hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate h_adj_exp

/-- **Canonical bridge constructor with the selected Simon-Lieb trichotomy
rate**.

This removes the explicit caller obligations `0 < M`, `M ≤ 1`, and
`((α : ℝ) + 1) * M ≤ simonLiebRate / 2` from
`canonical_bridge_from_simonLieb_adjacent`; the only remaining analytic input
is the adjacent correlation bound for the selected rate. -/
noncomputable def canonical_bridge_from_simonLieb_selected_rate_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(simonLiebTrichotomyBridgeRate α β J d))) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  canonical_bridge_from_simonLieb_adjacent hα hr d hf hβJd_pos hβJd_lt.le
    (simonLiebTrichotomyBridgeRate_pos hβJd_pos hβJd_lt)
    (simonLiebTrichotomyBridgeRate_le_one α β J d)
    (simonLiebTrichotomyBridgeRate_scaled_le_simonLiebRate_half α β J d)
    h_adj_exp

/-- **Canonical HLS sum existential** (exp-adjacent input form, full trichotomy). -/
theorem canonical_hls_sum
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
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
  have hβJ_pos := betaJ_pos_of_betaJ_two_d_pos (β := β) (J := J) (d := d) hβJd_pos
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_trichotomy_adjacent
    hα hr d hαd hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate
    h_adj_exp x₀ y₀

/-- **Canonical HLS sum using the selected Simon-Lieb trichotomy bridge
rate**. -/
theorem canonical_hls_sum_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(simonLiebTrichotomyBridgeRate α β J d)))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  canonical_hls_sum hα hr d hαd hf hβJd_pos hβJd_lt.le
    (simonLiebTrichotomyBridgeRate_pos hβJd_pos hβJd_lt)
    (simonLiebTrichotomyBridgeRate_le_one α β J d)
    (simonLiebTrichotomyBridgeRate_scaled_le_simonLiebRate_half α β J d)
    h_adj_exp x₀ y₀

/-- **Canonical bound provider** (full trichotomy). -/
theorem canonical_bound_provider
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r :=
  (canonical_bridge_from_simonLieb_adjacent hα hr d hf hβJd_pos hβJd_le
    hM_pos hM_le_one hMrate h_adj_exp).bound

/-- **Canonical bound provider using the selected Simon-Lieb trichotomy bridge
rate**. -/
theorem canonical_bound_provider_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(simonLiebTrichotomyBridgeRate α β J d))) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      simonLiebTrichotomyBridgeRate α β J d * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r :=
  (canonical_bridge_from_simonLieb_selected_rate_adjacent
    hα hr d hf hβJd_pos hβJd_lt h_adj_exp).bound

/-- **Canonical active provider** (from `Ferromagnetic` + `0 < β·J`). -/
theorem canonical_active_provider
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
  correlationInfinite_pair_active_of_betaJ_pos hf.hβ hβJ_pos

/-- **Canonical bridge constructor** (tanh-adjacent input form, full trichotomy). -/
def canonical_bridge_from_tanh_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  have hβJ_pos := betaJ_pos_of_betaJ_two_d_pos (β := β) (J := J) (d := d) hβJd_pos
  PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_tanh_adjacent
    hα hr d hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
    hMrate_htep h_adj_tanh

/-- **Canonical bridge constructor with the selected tanh-compatible
Simon-Lieb trichotomy rate**.

This removes the explicit caller obligations `0 < M`, `M ≤ 1`,
`((α : ℝ) + 1) * M ≤ simonLiebRate / 2`, and
`M ≤ highTempExpRate β J` from `canonical_bridge_from_tanh_adjacent`; the only
remaining analytic input is the adjacent tanh-power correlation bound. -/
noncomputable def canonical_bridge_from_tanh_selected_rate_adjacent
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  canonical_bridge_from_tanh_adjacent hα hr d hf hβJd_pos hβJd_lt.le
    (simonLiebTanhTrichotomyBridgeRate_pos hβJd_pos hβJd_lt)
    (simonLiebTanhTrichotomyBridgeRate_le_one α β J d)
    (simonLiebTanhTrichotomyBridgeRate_scaled_le_simonLiebRate_half α β J d)
    (simonLiebTanhTrichotomyBridgeRate_le_highTempExpRate α β J d)
    h_adj_tanh

/-- **Canonical HLS sum existential** (tanh-adjacent input form, full trichotomy). -/
theorem canonical_hls_sum_tanh
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate_sl : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (hMrate_htep : M ≤ highTempExpRate β J)
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
  have hβJ_pos := betaJ_pos_of_betaJ_two_d_pos (β := β) (J := J) (d := d) hβJd_pos
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_trichotomy_tanh_adjacent
    hα hr d hαd hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hM_le_one hMrate_sl
    hMrate_htep h_adj_tanh x₀ y₀

/-- **Canonical HLS sum using the selected tanh-compatible Simon-Lieb
trichotomy bridge rate**. -/
theorem canonical_hls_sum_tanh_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
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
  canonical_hls_sum_tanh hα hr d hαd hf hβJd_pos hβJd_lt.le
    (simonLiebTanhTrichotomyBridgeRate_pos hβJd_pos hβJd_lt)
    (simonLiebTanhTrichotomyBridgeRate_le_one α β J d)
    (simonLiebTanhTrichotomyBridgeRate_scaled_le_simonLiebRate_half α β J d)
    (simonLiebTanhTrichotomyBridgeRate_le_highTempExpRate α β J d)
    h_adj_tanh x₀ y₀

/-- **Canonical bound provider using the selected tanh-compatible Simon-Lieb
trichotomy bridge rate**. -/
theorem canonical_bound_provider_tanh_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      simonLiebTanhTrichotomyBridgeRate α β J d *
          (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r :=
  (canonical_bridge_from_tanh_selected_rate_adjacent
    hα hr d hf hβJd_pos hβJd_lt h_adj_tanh).bound

/-- **Canonical positive K extraction** from the HLS sum bound. -/
theorem canonical_K_pos_from_hls_sum
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K :=
  let ⟨K, hK_pos, _⟩ := canonical_hls_sum
    hα hr d hαd hf hβJd_pos hβJd_le hM_pos hM_le_one hMrate h_adj_exp x₀ y₀
  ⟨K, hK_pos⟩

/-- **Canonical zero-anchor HLS sum** (= full-trichotomy `canonical_hls_sum` at `(0, 0)`). -/
theorem canonical_hls_sum_zero_anchor
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M) (hM_le_one : M ≤ 1)
    (hMrate : ((α : ℝ) + 1) * M ≤ simonLiebRate β J d / 2)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  canonical_hls_sum hα hr d hαd hf hβJd_pos hβJd_le hM_pos hM_le_one
    hMrate h_adj_exp 0 0

/-- **Canonical zero-anchor HLS sum using the selected Simon-Lieb trichotomy
bridge rate**. -/
theorem canonical_hls_sum_zero_anchor_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-(simonLiebTrichotomyBridgeRate α β J d))) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  canonical_hls_sum_selected_rate hα hr d hαd hf hβJd_pos hβJd_lt
    h_adj_exp 0 0

/-- **Canonical zero-anchor HLS sum using the selected tanh-compatible
Simon-Lieb trichotomy bridge rate**. -/
theorem canonical_hls_sum_zero_anchor_tanh_selected_rate
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_lt : β * J * (2 * d) < 1)
    (h_adj_tanh : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 w) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z}
      ≤ K :=
  canonical_hls_sum_tanh_selected_rate hα hr d hαd hf hβJd_pos hβJd_lt
    h_adj_tanh 0 0

end Ambient
end IsingModel
