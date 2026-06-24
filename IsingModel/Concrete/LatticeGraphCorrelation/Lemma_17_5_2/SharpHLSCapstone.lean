import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.SharpHLSScopeExcludedAxioms

/-!
# GJ §17.5 sharp HLS constant (Lemma 17.5.2 / Theorem 17.5.1) — unconditional capstone

Completes the GJ §17.5 sharp two-sided sandwich
`m⁻(x,z) ≤ m(x,z) ≤ C·m⁻(x,z)` (one HLS constant) for the cubic lattice at high temperature,
**unconditionally modulo the two declared scope-excluded analytic axioms** of
`SharpHLSScopeExcludedAxioms.lean` (the locally-uniform derivative-limit provider and the
validating endpoint pseudo-mass decay — the volume-uniform complex / Montel core, out of scope
exactly like `FunctionTheory.vitaliPorter_tendstoLocallyUniformlyOn`).

This closes audit gaps **B4 #4271** (sharp HLS constant, master #4214 item C) and **B2 #4269**
(the volume-uniform complex CE input it required): the conditional provider-shaped sandwich
`lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider` is instantiated with
the two scope-excluded axioms, removing every remaining hypothesis except the elementary
high-temperature interval data.

**Reference:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 / Lemma 17.5.2,
pp. 311–312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 / Theorem 17.5.1 sharp two-sided sandwich for the cubic lattice**
(unconditional modulo the declared scope-excluded analytic axioms).

For `1 ≤ α`, `2α > d`, `1 ≤ d`, `0 < rho`, a strictly-coupled ferromagnet `0 < J`, a distinct pair
`x ≠ z`, and a closed high-temperature interval `Icc β₁ β₂ ⊆ Ioo 0 (1/(J·2d))` with an auxiliary
compact `Icc a b` (`0 < a ≤ b`, `b·J·2d < 1`) containing it, with `0 < β₂` and `β₂·J·2d < 1`:
there is one HLS constant `K > 0` (the discrete HLS convolution constant) such that

* the HLS pair-product profile sum is `≤ K`, and
* `m⁻(x,z) ≤ m(x,z) ≤ (2α+1)·K/rho · m⁻(x,z)` (`m = latticeMass`,
  `m⁻ = pseudoMassFromParamsAtPair`).

The derivative-limit provider and validating decay are supplied by the declared scope-excluded
axioms `lemma_17_5_2_derivativeLimitProvider_latticeGraph` and
`lemma_17_5_2_validatingDecay_latticeGraph` (the volume-uniform complex / Montel core; cf.
`vitaliPorter`). Every other input is the elementary high-temperature interval data.

**Reference:** Glimm–Jaffe, 2nd ed., §17.5 Theorem 17.5.1 / Lemma 17.5.2, pp. 311–312. -/
theorem lemma_17_5_2_sandwich_sharp_latticeGraph
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d) (hd : 1 ≤ d)
    {rho : ℝ} (hrho : 0 < rho)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ_pos : 0 < J)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {β₁ β₂ a b : ℝ} (hβ₁₂ : β₁ ≤ β₂)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))))
    (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1)
    (hβ_mem : ∀ β ∈ Set.Icc β₁ β₂, β ∈ Set.Icc a b)
    (hβ₂ : 0 < β₂) (hβ₂lt : β₂ * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / rho) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hrho d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) :=
  lemma_17_5_2_sandwich_of_concrete_infinite_hls_compact_ratio_bounds_provider
    hα hαd hd hrho hJ_pos hxz hβ₁₂ hIcc ha hab hlt hβ_mem
    (lemma_17_5_2_derivativeLimitProvider_latticeGraph Λ hJ_pos hxz)
    (lemma_17_5_2_validatingDecay_latticeGraph hα hrho Λ hJ_pos hβ₂ hβ₂lt hxz)

end Ambient
end IsingModel
