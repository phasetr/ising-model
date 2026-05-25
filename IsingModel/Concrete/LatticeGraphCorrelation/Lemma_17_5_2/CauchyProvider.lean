import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeProfileInputs

/-!
# GJ §17.5 Lemma 17.5.2 capstone — Cauchy-provider input

This module packages the named compact-Cauchy derivative-profile inputs as a
`Lemma_17_5_2_DerivativeLimitProvider`, without importing any downstream HLS
assembly layer.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 named Cauchy input extracted from a provider**:
the locally uniform derivative-limit provider supplies the closed-interval
metric Cauchy input used by the named Cauchy-provider route. -/
theorem lemma_17_5_2_named_metricCauchy_on_Icc_of_derivative_limit_provider
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} {x z : Fin d → ℤ}
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z) :
    Lemma_17_5_2_DerivativeProfileMetricCauchyOnIcc Λ J x z := by
  intro β₁ β₂ hIcc
  exact
    lemma_17_5_2_derivative_limit_provider_metricCauchy_on_Icc
      (Λ := Λ) (J := J) (x := x) (z := z) hprovider hIcc

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider from named Cauchy
inputs**: the named compact-interval metric Cauchy and pointwise convergence
inputs supply the provider used by downstream HLS and concrete capstone layers.
-/
theorem lemma_17_5_2_derivative_limit_provider_of_named_metricCauchy_on_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcauchy : Lemma_17_5_2_DerivativeProfileMetricCauchyOnIcc Λ J x z)
    (hpoint : Lemma_17_5_2_DerivativeProfilePointwiseLimit Λ J x z g') :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z :=
  lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
    Λ J x z g' hcauchy hpoint

end Ambient
end IsingModel
