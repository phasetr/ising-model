import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicHighTemp

/-!
# GJ §17.5 Lemma 17.5.2 capstone — HLS constants and denominator comparisons

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
collects the discrete Hardy--Littlewood--Sobolev constant existence wrapper,
the uniform convolution constant under the Lemma 17.5.2 banner, and the
finite-volume / infinite-volume HLS denominator-comparison predicates.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 constant existence (alias of
`discrete_hls_constant`)**: under `2α > d` the discrete Hardy--Littlewood--Sobolev
constant exists. This is the existence side of the constant `C > 0` appearing
in the Lemma 17.5.2 upper-bound side `m ≤ C · m⁻`.

The actual quantitative bound matching the GJ Lipschitz argument (Theorem
17.5.1 proof, p.~312) is a future PR; this lemma exposes the existence of a
positive constant under the HLS hypothesis so that downstream statements can
quote `C` without re-stating its existence proof.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_constant_existence (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, 0 < C :=
  discrete_hls_constant α d hαd

/-- **GJ §17.5 Lemma 17.5.2 HLS convolution constant**: under `2α > d`
there is a positive constant uniformly bounding the polynomial convolution
kernel
`∑_w (1 + dist x w)^(-α) * (1 + dist y w)^(-α)`.

This is the constant-form HLS input used in the upper-bound/Lipschitz side of
Lemma 17.5.2. It is stronger than the bare existence alias
`lemma_17_5_2_constant_existence`, because the returned constant carries the
actual convolution inequality needed downstream.

References: Glimm--Jaffe §17.5, Lemma 17.5.2 and Theorem 17.5.1 proof,
pp.~311--312. -/
theorem lemma_17_5_2_hls_convolution_constant (α d : ℕ) (hαd : 2 * α > d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y w : ℝ) ^ (-(α : ℝ)) ≤ C :=
  IsingModel.discrete_hls_convolution_constant α d hαd

/-- **GJ §17.5 Lemma 17.5.2 finite-stage HLS denominator comparison**:
the named scalar comparison between the concrete high-temperature
Lebowitz/susceptibility derivative bound and the HLS pseudo-mass denominator
term.  The constant `K` is intended to be chosen by
`lemma_17_5_2_hls_convolution_constant`; this predicate names the remaining
pointwise comparison needed before applying the pseudo-mass calculus.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
def Lemma_17_5_2_HLSDenominatorComparison
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J b : ℝ) (n : ℕ) (r s : ↑(Λ.volume n))
    (β : ℝ) (α : ℕ) (K : ℝ) (h : ℝ → ℝ) : Prop :=
  let M : ℝ := b * J * ↑(2 * d) / (1 - b * J * ↑(2 * d))
  J * M ^ 2 + J * (4 * ↑d) ≤
    K *
      IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} /
      (h β) ^ (2 * α)

/-- **GJ §17.5 Lemma 17.5.2 infinite-volume HLS derivative comparison**:
the exact denominator comparison needed by the abstract pseudo-mass calculus,
with `c(β) := correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {x,z}`:
`|c'(β)| ≤ K * c(β) / (h β)^(2α)`.

This is the infinite-volume counterpart of the finite-stage comparison after
the concrete derivative estimate has already been passed to the HLS denominator
shape.  It is intentionally still a hypothesis: proving it from Lebowitz plus
HLS and limits is the remaining substantive upper-bound step.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
def Lemma_17_5_2_InfiniteHLSDenominatorComparison
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (β : ℝ) (α : ℕ) (K : ℝ) (h : ℝ → ℝ) : Prop :=
  |deriv (fun β' =>
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z}) β| ≤
    K *
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} /
      (h β) ^ (2 * α)

/-- **GJ §17.5 Lemma 17.5.2 infinite-volume HLS Lipschitz to all-rate bridge**:
the named remaining analytic bridge from the HLS Lipschitz estimate for
`β ↦ (h β)^(2α+1)` to the all-admissible exponential-decay-rate estimate
needed by the `latticeMass` upper-bound assembly.

For a fixed HLS constant `K`, this predicate says that once the interval
Lipschitz estimate produced from the infinite-volume HLS denominator comparison
is available, every nonnegative validating exponential-decay rate at the right
endpoint `β₂` is bounded by `((2α+1)K/r) · m⁻(β₂)`.

This is intentionally a `Prop` hypothesis: proving it is the substantive
analytic step that remains between the current HLS/Lipschitz machinery and the
full HLS-uniform Lemma 17.5.2 upper bound.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
def Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ)
    (β₁ β₂ : ℝ) (K : ℝ) (h : ℝ → ℝ) : Prop :=
  ((∀ β' ∈ Set.Icc β₁ β₂,
      Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
    |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
      ↑(2 * α + 1) * K / r * (β₂ - β₁)) →
  ∀ a : NNReal,
    HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) (a : ℝ) →
      (a : ENNReal) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)

end Ambient
end IsingModel
