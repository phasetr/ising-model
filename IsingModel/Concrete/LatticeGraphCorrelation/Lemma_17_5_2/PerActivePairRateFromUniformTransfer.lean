import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalAllRateComparisonFromPairs
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# GJ §17.5 Lemma 17.5.2 Part B — per-active-pair rate bound from a uniform
`pseudoMassG` transfer bound

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
reduces the per-active-pair rate/pseudo-mass lower bound
`Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound` (the remaining analytic
input after PRs #3379, #3380) to a *uniform* transfer correlation bound of the
shape `correlationInfinite … {x, z} ≤ pseudoMassG α r ((a : ℝ)/K)`, holding for
every admissible decay rate `a` and every active pair `(x, z)`.

The existing pseudo-mass calculus already turns such a `pseudoMassG`-shaped
correlation upper bound, on the active window, into a pseudo-mass *lower* bound
`(a : ℝ)/K ≤ m⁻(x, z)` (`pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG`).
What remains genuinely open is producing the uniform `pseudoMassG` bound itself:
the existential decay constant `C` of `HasExponentialDecay` is rate-dependent and
too coarse on nearby pairs, so a prefactor-free uniform pair bound (the
transfer-matrix content of GJ pp.~311--312) is still required.  At `h = 0` the
truncated and full two-point functions coincide (`truncated2Infinite_h_zero`), so
`HasExponentialDecay` is literally exponential decay of the correlation, which is
the analytic source the uniform `pseudoMassG` bound below abstracts.

Tracking issue: <https://github.com/phasetr/ising-model/issues/3378>
(parent <https://github.com/phasetr/ising-model/issues/1645>).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of the scaled rate**: for `0 < K` and a nonnegative rate
`a : NNReal`, the quotient `(a : ℝ)/K` is nonnegative. -/
theorem rate_div_nonneg_of_K_pos {K : ℝ} (hK : 0 < K) (a : NNReal) :
    0 ≤ (a : ℝ) / K :=
  div_nonneg (NNReal.coe_nonneg a) hK.le

/-- **GJ §17.5 Lemma 17.5.2 uniform `pseudoMassG` transfer bound (hypothesis
form)**: with a positive scale `K`, for every admissible nonnegative decay rate
`a` at `(⟨J, 0, β⟩)` and every active pair `(x, z)`, the correlation is bounded
by the pseudo-mass profile `pseudoMassG α r ((a : ℝ)/K)`.

This is the prefactor-free uniform pair bound supplied by the transfer-matrix
step of GJ Lemma 17.5.2; it is kept as a named hypothesis.  Given it, the
pseudo-mass calculus closes the per-active-pair rate lower bound (below).

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
def Lemma_17_5_2_UniformTransferPseudoMassGBound {α d : ℕ} {r : ℝ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        ∀ x z : Fin d → ℤ,
          ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z →
            Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
              ≤ pseudoMassG α r ((a : ℝ) / K)

/-- **Per-pair pseudo-mass lower bound from a scaled `pseudoMassG` correlation
bound**: at an active pair, a correlation bound
`correlationInfinite … {x, z} ≤ pseudoMassG α r ((a : ℝ)/K)` gives the pseudo-mass
lower bound `(a : ℝ)/K ≤ m⁻(x, z)`.

This is the `t = (a : ℝ)/K` instance of
`pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG`, with nonnegativity from
`rate_div_nonneg_of_K_pos` and the active window from the active-pair predicate. -/
theorem pseudoMassFromParamsAtPair_ge_rate_div_of_corr_le_pseudoMassG
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (a : NNReal) {K : ℝ} (hK : 0 < K) {x z : Fin d → ℤ}
    (hactive : ActivePseudoMassPair Λ p x z)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ pseudoMassG α r ((a : ℝ) / K)) :
    (a : ℝ) / K ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z :=
  pseudoMassFromParamsAtPair_ge_of_corr_le_pseudoMassG hα hr d Λ p x z
    (rate_div_nonneg_of_K_pos hK a) hactive.2 hle

/-- **Per-active-pair rate bound from the uniform `pseudoMassG` transfer bound**:
the uniform `pseudoMassG` correlation bound implies the named per-active-pair
rate/pseudo-mass lower bound `Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound`. -/
theorem lemma_17_5_2_per_active_pair_rate_of_uniform_transfer_pseudoMassG
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {K : ℝ}
    (hU : Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
            Λ J β K) :
    Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound hα hr Λ J β K := by
  obtain ⟨hK, hb⟩ := hU
  refine ⟨hK, fun a ha x z hxz => ?_⟩
  exact pseudoMassFromParamsAtPair_ge_rate_div_of_corr_le_pseudoMassG hα hr Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) a hK hxz (hb a ha x z hxz)

/-- **GJ §17.5 Lemma 17.5.2 all-rate comparison from the uniform `pseudoMassG`
transfer bound**: an active-pair witness plus the uniform `pseudoMassG` transfer
bound yields the system-level all-rate comparison at coefficient `ofReal K`. -/
theorem lemma_17_5_2_global_all_rate_comparison_of_uniform_transfer_pseudoMassG
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {K : ℝ} {x₀ z₀ : Fin d → ℤ}
    (hwit : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x₀ z₀)
    (hU : Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
            Λ J β K) :
    Lemma_17_5_2_GlobalAllRateComparison hα hr Λ J β (ENNReal.ofReal K) :=
  lemma_17_5_2_global_all_rate_comparison_of_per_active_pair_rate_pseudoMass_lower_bound
    hα hr Λ J β hwit
    (lemma_17_5_2_per_active_pair_rate_of_uniform_transfer_pseudoMassG
      hα hr Λ J β hU)

/-- **GJ §17.5 Lemma 17.5.2 upper bound from the uniform `pseudoMassG` transfer
bound**: at an active pair `(x, z)`, the uniform `pseudoMassG` correlation bound
closes the named `latticeMass` upper-bound predicate at coefficient `ofReal K`.

This is the cleanest current entry point to `Lemma_17_5_2_UpperBound` whose sole
remaining substantive input is the transfer-matrix uniform `pseudoMassG`
correlation bound. -/
theorem lemma_17_5_2_upper_bound_of_uniform_transfer_pseudoMassG
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {K : ℝ} {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hU : Lemma_17_5_2_UniformTransferPseudoMassGBound (α := α) (r := r)
            Λ J β K) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z (ENNReal.ofReal K) :=
  lemma_17_5_2_upper_bound_of_per_active_pair_rate_pseudoMass_lower_bound
    hα hr Λ J β hxz
    (lemma_17_5_2_per_active_pair_rate_of_uniform_transfer_pseudoMassG
      hα hr Λ J β hU)

end Ambient
end IsingModel
