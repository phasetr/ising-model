import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# HLS bridge from Simon-Lieb: core constructors and consumers

Core child module of the build-speed split of `HLSBridgeFromSimonLieb`.
Houses the end-to-end `PseudoMassLatticeDistanceBridge` Simon-Lieb
constructors (the shared hub referenced by every sibling module), the HLS sum
existential consumers, and the bridge field providers.  The Tanh, Variants, and
Canonical child modules import this file.  See the umbrella
`HLSBridgeFromSimonLieb` for the full narrative and references.
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
- `0 < β·J·(2d) ≤ 1` (Simon-Lieb nonnegative-rate regime);
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

end Ambient
end IsingModel
