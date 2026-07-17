import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.UpperBound
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferExpDecay
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSConstants
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Predicates

/-!
# GJ §17.5 Lemma 17.5.2 capstone — Step 115 path-rate bridge

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development. It
connects the infinite-volume HLS Lipschitz package with the Step 115 all-rate
path bound, without importing the finite derivative-limit/HLS package.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 all-decay-rate bound from the Step 115 path rate**:
if the Step 115 path rate `-log(tanh(βJ))` is bounded by a target multiple of
the endpoint concrete pseudo-mass, then every nonnegative validating
exponential-decay rate is bounded by that same target.

The proof transfers the validating decay rate to the cubic exhaustion, applies
the all-rate Step 115 estimate, and composes with the supplied scalar
comparison. -/
theorem lemma_17_5_2_all_decay_rates_le_of_path_rate_le
    {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (x z : Fin d → ℤ) (C : ENNReal)
    (hpath_le :
      ENNReal.ofReal (-Real.log (Real.tanh (β * J))) ≤
        C *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        (a : ENNReal) ≤
          C *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  intro a ha
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  have ha_cubic :
      HasExponentialDecay d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) :=
    HasExponentialDecay_transfer_exhaustion Λ (Ambient.cubicExhaustion d) hf ha
  exact (HasExponentialDecay_rate_le_neg_log_tanh_betaJ hd hJ hβ ha_cubic).trans
    hpath_le

/-- **GJ §17.5 Lemma 17.5.2 upper bound from the Step 115 path-rate scalar
comparison**: the direct all-decay-rate estimate from
`lemma_17_5_2_all_decay_rates_le_of_path_rate_le` closes the named
`latticeMass` upper-bound predicate. -/
theorem lemma_17_5_2_upper_bound_of_path_rate_le
    {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (x z : Fin d → ℤ) (C : ENNReal)
    (hpath_le :
      ENNReal.ofReal (-Real.log (Real.tanh (β * J))) ≤
        C *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z C := by
  exact lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β x z C
    (lemma_17_5_2_all_decay_rates_le_of_path_rate_le
      hα hr hd Λ hJ hβ x z C hpath_le)

/-- **GJ §17.5 Lemma 17.5.2 sandwich from lower decay and the Step 115
path-rate scalar comparison**: combine the direct path-rate upper side with the
validating endpoint pseudo-mass decay lower side. -/
theorem lemma_17_5_2_sandwich_of_decay_and_path_rate_le
    {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {x z : Fin d → ℤ} {C : ENNReal}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z))
    (hpath_le :
      ENNReal.ofReal (-Real.log (Real.tanh (β * J))) ≤
        C *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      C *
        ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay
    (lemma_17_5_2_upper_bound_of_path_rate_le
      hα hr hd Λ hJ hβ x z C hpath_le)

/-- **GJ §17.5 Lemma 17.5.2 all-rate bridge from the Step 115 path-rate
comparison**: the named infinite HLS Lipschitz all-rate bridge follows once the
Step 115 path rate `-log(tanh(β₂J))` is bounded by the HLS Lipschitz
coefficient times the endpoint pseudo-mass.

The proof transfers any target-exhaustion validating decay rate to the cubic
exhaustion, applies the all-rate Step 115 bound, and then uses the supplied
scalar comparison. -/
theorem lemma_17_5_2_infinite_hls_lipschitz_all_rate_bridge_of_path_rate_le_hls
    {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {β₁ β₂ K : ℝ} (hβ₂ : 0 < β₂)
    (x z : Fin d → ℤ) (h : ℝ → ℝ)
    (hpath_le :
      ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
        ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) :
    Lemma_17_5_2_InfiniteHLSLipschitzAllRateBridge
      hα hr Λ J x z β₁ β₂ K h := by
  intro _hlip
  exact
    lemma_17_5_2_all_decay_rates_le_of_path_rate_le
      hα hr hd Λ hJ hβ₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) hpath_le

/-- **GJ §17.5 Lemma 17.5.2 upper bound from an infinite HLS Lipschitz package
and path-rate comparison**: after the infinite HLS layer has produced the
existential Lipschitz package, the Step 115 path-rate scalar comparison
discharges the named all-rate bridge and closes the upper-bound predicate. -/
theorem lemma_17_5_2_upper_bound_of_exists_infinite_hls_lipschitz_and_path_rate_le
    {d α : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₂ : 0 < β₂) {h : ℝ → ℝ}
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
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
        Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r))) := by
  obtain ⟨K, hK, hK_conv, _hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun _hcomp hpath_le => ?_⟩
  exact
    lemma_17_5_2_upper_bound_of_path_rate_le
      hα hr hd Λ hJ hβ₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) hpath_le

/-- **GJ §17.5 Lemma 17.5.2 sandwich from an infinite HLS Lipschitz package
and path-rate comparison**: combine the preceding infinite-HLS/path-rate
upper-bound package with the lower validating pseudo-mass decay input. -/
theorem lemma_17_5_2_sandwich_of_exists_infinite_hls_lipschitz_and_path_rate_le
    {d α : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₂ : 0 < β₂) {h : ℝ → ℝ}
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
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, _hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun _hcomp hpath_le => ?_⟩
  exact
    lemma_17_5_2_sandwich_of_decay_and_path_rate_le
      hα hr hd hJ hβ₂ hdecay hpath_le

/-- **GJ §17.5 Lemma 17.5.2 capstone from an infinite HLS Lipschitz package
and path-rate comparison**: returns the HLS witness and, under the same
denominator-comparison and path-rate premises, both the named upper-bound
predicate and the displayed two-sided sandwich for one constant. -/
theorem lemma_17_5_2_capstone_of_exists_infinite_hls_lipschitz_and_path_rate_le
    {d α : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 < J) {x z : Fin d → ℤ} {β₁ β₂ : ℝ}
    (hβ₂ : 0 < β₂) {h : ℝ → ℝ}
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
      ((∀ β' ∈ Set.Icc β₁ β₂,
          Lemma_17_5_2_InfiniteHLSDenominatorComparison Λ J x z β' α K h) →
        ENNReal.ofReal (-Real.log (Real.tanh (β₂ * J))) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z) →
        Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
          (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) ∧
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r) *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β₂⟩ : IsingParams ℝ) x z)) := by
  obtain ⟨K, hK, hK_conv, _hlip⟩ := hpkg
  refine ⟨K, hK, hK_conv, fun _hcomp hpath_le => ?_⟩
  have hupper :
      Lemma_17_5_2_UpperBound hα hr Λ J β₂ x z
        (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) :=
    lemma_17_5_2_upper_bound_of_path_rate_le
      hα hr hd Λ hJ hβ₂ x z
      (ENNReal.ofReal (((2 * α + 1 : ℕ) : ℝ) * K / r)) hpath_le
  exact ⟨hupper,
    lemma_17_5_2_sandwich_of_decay_and_path_rate_le
      hα hr hd hJ hβ₂ hdecay hpath_le⟩

end Ambient
end IsingModel
