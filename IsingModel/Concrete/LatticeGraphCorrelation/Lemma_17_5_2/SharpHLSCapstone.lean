import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.SharpHLSScopeExcludedAxioms
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# GJ §17.5 sharp HLS constant (Lemma 17.5.2 / Theorem 17.5.1) — cubic-exhaustion capstone

Completes the GJ §17.5 sharp two-sided sandwich
`m⁻(x,z) ≤ m(x,z) ≤ C·m⁻(x,z)` (one HLS constant) for the cubic-exhaustion infinite-volume mass at
high temperature, with the **only** remaining inputs being:

1. the **single declared scope-excluded analytic axiom** of `SharpHLSScopeExcludedAxioms.lean` —
   the locally-uniform derivative-limit provider (Montel / Vitali–Porter normal-families core, out
   of scope exactly like `FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`); and
2. the **per-pair profile lower bound** `pseudoMassG α rho (−log(β₂·J·2d)) ≤ correlationInfinite
   {x,z}` as an explicit **hypothesis** — exactly the same validating-decay input the *non-sharp*
   uniform sandwich `lemma_17_5_2_high_temp_sandwich_uniform_transfer` already carries. This is
   **not** axiomatized: its unconditional `∀ x ≠ z` form is *false* (the project's own no-go B3
   #4270 shows it fails for far pairs, where `correlationInfinite → 0` while the pseudo-mass `→ ∞`).

This discharges audit gaps **B4 #4271** (sharp HLS constant, master #4214 item C) and **B2 #4269**
(the volume-uniform complex CE input the derivative-limit provider represents).

**Reference:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 / Lemma 17.5.2,
pp. 311–312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 / Theorem 17.5.1 sharp two-sided sandwich for the cubic-exhaustion
infinite-volume mass** (modulo the declared scope-excluded derivative-limit axiom and the per-pair
profile lower bound).

For `1 ≤ α`, `2α > d`, `1 ≤ d`, `0 < rho`, a strictly-coupled ferromagnet `0 < J`, a distinct pair
`x ≠ z`, a closed high-temperature interval `Icc β₁ β₂ ⊆ Ioo 0 (1/(J·2d))` with an auxiliary
compact `Icc a b` (`0 < a ≤ b`, `b·J·2d < 1`) containing it, with `0 < β₂`, `β₂·J·2d < 1`, and the
per-pair profile lower bound `hprofile`: there is one HLS constant `K > 0` such that

* the HLS pair-product profile sum is `≤ K`, and
* `m⁻(x,z) ≤ m(x,z) ≤ (2α+1)·K/rho · m⁻(x,z)` (`m = latticeMass`,
  `m⁻ = pseudoMassFromParamsAtPair`) for the cubic exhaustion.

The derivative-limit provider is supplied by the declared scope-excluded axiom
`lemma_17_5_2_derivativeLimitProvider_latticeGraph` (the volume-uniform complex / Montel core; cf.
`vitaliPorter`); the validating endpoint pseudo-mass decay is *proven* from `hprofile` and the
active-range membership via `HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`.

**Reference:** Glimm–Jaffe, 2nd ed., §17.5 Theorem 17.5.1 / Lemma 17.5.2, pp. 311–312. -/
theorem lemma_17_5_2_sandwich_sharp_cubicExhaustion
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hβ₂ : 0 < β₂) (hβ₂lt : β₂ * J * ↑(2 * d) < 1)
    (hprofile :
      pseudoMassG α rho (-Real.log (β₂ * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hβ₂J_pos : 0 < β₂ * J := mul_pos hβ₂ hJ_pos
  -- Active-range membership of the endpoint correlation (from `0 < β₂·J`).
  have hcorr :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos hβ₂ hβ₂J_pos x z hxz
  -- Validating endpoint pseudo-mass decay, PROVEN from the per-pair profile bound.
  have hdecay :
      HasExponentialDecay d (Ambient.cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)
        (pseudoMassFromParamsAtPair hα hrho d (Ambient.cubicExhaustion d)
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
      hα hrho (Ambient.cubicExhaustion d) hJ_pos.le hβ₂ hβ₂lt hcorr hprofile
  exact
    lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
      hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
      (lemma_17_5_2_derivativeLimitProvider_latticeGraph (Ambient.cubicExhaustion d) hJ_pos hxz)
      hdecay

end Ambient
end IsingModel
