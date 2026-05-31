import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb

/-!
# HLS bridge ferromagnetic-input and convenience aliases

GJ-proposition-unit bundle of ferromagnetic-form aliases and convenience
access wrappers for the HLS bridge constructors
(#3188/#3189/#3190/#3191).

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Ferromagnetic-input aliases -/

/-- **`PseudoMassLatticeDistanceBridge` end-to-end constructor taking the
`Ferromagnetic ⟨J, 0, β⟩` predicate directly**. -/
def PseudoMassLatticeDistanceBridge_of_simonLieb_ferromagnetic
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ_pos : 0 < β * J := by
    by_contra h
    push Not at h
    have : β * J * (2 * d) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h h2d_nn
    linarith
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    hα hr d hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp

/-- **HLS sum existential taking the `Ferromagnetic ⟨J, 0, β⟩` predicate**. -/
theorem tsum_correlationInfinite_pair_product_le_const_of_simonLieb_ferromagnetic
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
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
      ≤ K := by
  have h2d_nn : (0 : ℝ) ≤ 2 * d := by positivity
  have hβJ_pos : 0 < β * J := by
    by_contra h
    push Not at h
    have : β * J * (2 * d) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h h2d_nn
    linarith
  exact tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hf.hJ hf.hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp x₀ y₀

/-- **Active range from `Ferromagnetic ⟨J, 0, β⟩` + `0 < β·J`**. -/
theorem correlationInfinite_pair_active_of_ferromagnetic
    {d : ℕ} {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (hβJ_pos : 0 < β * J) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
  correlationInfinite_pair_active_of_betaJ_pos hf.hβ hβJ_pos

/-! ## `0 ≤ β · J` derivation from ferromagnetic -/

/-- **`0 ≤ β · J` from `Ferromagnetic ⟨J, 0, β⟩`** (helper). -/
theorem ferromagnetic_betaJ_nonneg {J β : ℝ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J :=
  mul_nonneg hf.hβ.le hf.hJ

/-- **`0 ≤ β · J · (2d)` from `Ferromagnetic ⟨J, 0, β⟩`** (helper). -/
theorem ferromagnetic_betaJ_two_d_nonneg {J β : ℝ} {d : ℕ}
    (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)) :
    0 ≤ β * J * (2 * d) :=
  mul_nonneg (ferromagnetic_betaJ_nonneg hf) (by positivity)

/-! ## Per-pair (not zero-anchored) accessors -/

/-- **Per-pair pseudo-mass-distance bound from the HLS bridge**.

Convenience access: given a fully-built `PseudoMassLatticeDistanceBridge`
and a distinct pair `(x, z)`, return the `bound` field at this pair. -/
theorem bridge_bound_at_pair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr d J β)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    bridge.M_inf * (latticeDistance d x z : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z * r :=
  bridge.bound x z hxz

/-- **Per-pair active range from the HLS bridge**. -/
theorem bridge_active_at_pair
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr d J β)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 :=
  bridge.active x z hxz

/-! ## High-temperature constraint helpers -/

/-- **`β · J · (2d) ≤ 1` from `β · J ≤ 1/(2d)`** (helper).

Convenience implication for the upper high-temperature constraint when
expressed as a per-coupling bound. -/
theorem betaJ_two_d_le_one_of_betaJ_le_inv {β J : ℝ} {d : ℕ}
    (hd : 0 < d) (hbβJ : β * J ≤ 1 / (2 * d)) :
    β * J * (2 * d) ≤ 1 := by
  have h2d_pos : (0 : ℝ) < 2 * d := by positivity
  rw [le_div_iff₀ h2d_pos] at hbβJ
  exact hbβJ

end Ambient
end IsingModel
