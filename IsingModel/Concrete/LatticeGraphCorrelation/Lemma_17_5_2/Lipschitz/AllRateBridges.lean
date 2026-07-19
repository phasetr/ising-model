import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.BetaDerivBridges
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicHighTemp

/-!
# GJ §17.5 Lemma 17.5.2 capstone — all-rate upper-bound and sandwich bridges

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Lipschitz` development.
It converts the infinite-volume HLS/Lipschitz layer into the named all-rate
`latticeMass` upper-bound and sandwich packages, including the existential-package
and HLS-constant forms.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an infinite-volume HLS Lipschitz
all-rate bridge**: once the HLS/Lipschitz layer has produced the interval
Lipschitz estimate for `β ↦ (h β)^(2α+1)`, the named bridge
`Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge` converts it into the
all-admissible-rate estimate, and the order-theoretic upper-bound assembly
closes `Lemma_17_5_2_UpperBound`.

This theorem deliberately does not re-prove the interval Lipschitz estimate;
that is supplied by
`lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant`.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ) (β₁ β₂ K : ℝ) (h : ℝ → ℝ)
    (hlip :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / r * (β₂ - β₁))
    (hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hr Λ J x z β₁ β₂ K h) :
    Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) := by
  exact lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β₂ x z
    (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) (hbridge hlip)

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an infinite-volume HLS Lipschitz
all-rate bridge**: once the lower pseudo-mass decay side is available at
`β₂`, the preceding upper-bound bridge gives the full conditional sandwich.

The theorem keeps the last analytic step explicit as
`Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge`, but removes all remaining
order-theoretic assembly from downstream work.

References: Glimm--Jaffe §17.5, Theorem 17.5.1 proof and Lemma 17.5.2,
pp.~311--312. -/
theorem lemma_17_5_2_sandwich_of_infinite_hls_lipschitz_all_rate_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} {x z : Fin d → ℤ} {β₁ β₂ K : ℝ} {h : ℝ → ℝ}
    (hlip :
      (∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
          ↑(2 * α + 1) * K / r * (β₂ - β₁))
    (hbridge :
      Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
        hα hr Λ J x z β₁ β₂ K h)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
        ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) := by
  have hupper :
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) :=
    lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
      hα hr Λ J x z β₁ β₂ K h hlip hbridge
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay hupper

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an existential infinite HLS
Lipschitz package and all-rate bridge**: if the infinite-volume HLS/Lipschitz
layer has produced an existential HLS constant package, and the named
all-rate bridge is available for the returned constant, then the named
`latticeMass` upper-bound predicate follows.

This avoids re-elaborating the heavy differentiability hypotheses of
`lemma_17_5_2_infinite_pseudoMass_pow_succ_lipschitz_of_hls_constant`; callers
pass that theorem's existential output directly. -/
theorem lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J : ℝ) (x z : Fin d → ℤ)
    (β₁ β₂ : ℝ) (h : ℝ → ℝ)
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁))) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
          hα hr Λ J x z β₁ β₂ K h →
        Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv, hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun hbridge => ?_⟩
  exact lemma_17_5_2_upper_bound_of_infinite_hls_lipschitz_all_rate_bridge
    hα hr Λ J x z β₁ β₂ K h hlip hbridge

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an existential infinite HLS
Lipschitz package and all-rate bridge**: combine the preceding existential
upper-bound package with the lower pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_exists_infinite_hls_lipschitz_bridge
    {d α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} {x z : Fin d → ℤ}
    {β₁ β₂ : ℝ} {h : ℝ → ℝ}
    (hpkg :
      ∃ K : ℝ, 0 < K ∧
        (∀ x' y' : Fin d → ℤ,
          ∑' w : Fin d → ℤ,
              (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
              (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
        ((∀ β' ∈ Set.Icc β₁ β₂,
            Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
          |(h β₂) ^ (2 * α + 1) - (h β₁) ^ (2 * α + 1)| ≤
            ↑(2 * α + 1) * K / r * (β₂ - β₁)))
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      (Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
          hα hr Λ J x z β₁ β₂ K h →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_bridge
      hα hr Λ J x z β₁ β₂ h hpkg
  refine ⟨K, hK, hK_conv, fun hbridge => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay (hupper hbridge)

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant upper-bound package**: under the
HLS exponent condition, choose a positive convolution constant `K`. If every
admissible nonnegative exponential-decay rate is bounded by the HLS Lipschitz
coefficient `(2α+1)K/r` times the concrete pseudo-mass, then the named
Lemma 17.5.2 upper-bound predicate follows.

This fixes the exact all-rate target for the remaining analytic/HLS proof:
the future work should prove the premise for the returned HLS constant `K`,
then this theorem closes the `latticeMass` upper side by the order-theoretic
assembly in `Predicates`. -/
theorem lemma_17_5_2_hls_upper_bound_of_all_decay_rates_le
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)) →
        Lemma_17_5_2_UpperBound hα hr Λ J β x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv⟩ := lemma_17_5_2_hls_convolution_constant α d hαd
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  exact lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β x z
    (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) hdecay_le

/-- **GJ §17.5 Lemma 17.5.2 HLS-constant sandwich package**: once the
pseudo-mass rate itself validates exponential decay, the same HLS convolution
constant package reduces the full sandwich to the all-admissible-decay-rate
upper estimate.

This is the direct capstone shape for the remaining HLS proof: provide the
all-rate premise for the returned constant `K`, and this theorem returns
`ofReal m⁻ ≤ latticeMass ≤ ((2α+1)K/r) · ofReal m⁻`. -/
theorem lemma_17_5_2_hls_sandwich_of_decay_and_all_decay_rates_le
    {d α : ℕ} (hα : 1 ≤ α) (hαd : 2 * α > d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x' y' : Fin d → ℤ,
        ∑' w : Fin d → ℤ,
            (1 + latticeDistance d x' w : ℝ) ^ (-(α : ℝ)) *
            (1 + latticeDistance d y' w : ℝ) ^ (-(α : ℝ)) ≤ K) ∧
      ((∀ a : NNReal,
          HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
            (a : ENNReal) ≤
              ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
                ENNReal.ofReal
                  (pseudoMassFromParamsAtPair hα hr d Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)) →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, hupper⟩ :=
    lemma_17_5_2_hls_upper_bound_of_all_decay_rates_le
      hα hαd hr Λ J β x z
  refine ⟨K, hK, hK_conv, fun hdecay_le => ?_⟩
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (hupper hdecay_le)

end Ambient
end IsingModel
