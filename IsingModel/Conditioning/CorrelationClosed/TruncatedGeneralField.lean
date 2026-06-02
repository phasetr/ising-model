import IsingModel.Inequalities.GHS.TruncatedDefs
import IsingModel.Conditioning.CorrelationClosed.GeneralField

/-!
# General external-field high-temperature expansion of connected correlations (GJ §18.5/§18.7)

The connected (truncated) correlation functions
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩` and the three-point Ursell function are
the objects whose decay the cluster expansion controls (GJ §18.5 convergence,
§18.7 decay of correlations). Here they are expressed at a general external
field `h` through the §18.3 master subset expansion of thermal averages
(`correlation_high_temp_expansion_general_h_subset_form`), each correlation
becoming a ratio of subset sums carrying the field weight `exp(β h ∑_i σ_i)`.

This is a finite-volume lattice Ising identity (no continuum limit); it is the
general-`h` foundation on which the connected-correlation cluster property and
decay estimates are built.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Subset-sum numerator of a thermal average at general `h`**: the common
building block `N[F] = ∑_{X⊆E} tanh(βJ)^{|X|} ∑_σ F(σ)(∏_{e∈X}σ_e) e^{βh∑σ}`
of the general-`h` high-temperature expansion. Abbreviation tying the
connected-correlation identities below to
`gibbsExpectation_high_temp_expansion_general_h_subset_form`. -/
noncomputable def highTempSubsetNumerator
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) : ℝ :=
  ∑ X ∈ G.edgeFinset.powerset,
    Real.tanh (p.β * p.J) ^ X.card *
      ∑ σ : Config ι,
        F σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
        Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))

/-- **Subset-sum denominator at general `h`**: `D = N[1]`, the `F = 1` case of
`highTempSubsetNumerator`, equal to `Z / cosh(βJ)^{|E|}`. -/
noncomputable def highTempSubsetDenominator
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  ∑ X ∈ G.edgeFinset.powerset,
    Real.tanh (p.β * p.J) ^ X.card *
      ∑ σ : Config ι,
        (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
        Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))

/-- **Gibbs expectation as `N[F] / D` at general `h`**: restatement of
`gibbsExpectation_high_temp_expansion_general_h_subset_form` through the named
numerator/denominator abbreviations. -/
theorem gibbsExpectation_eq_highTempSubsetNumerator_div_denominator
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    gibbsExpectation G p F =
      highTempSubsetNumerator G p F / highTempSubsetDenominator G p :=
  gibbsExpectation_high_temp_expansion_general_h_subset_form G p F

/-- **Correlation as `N[σ_A] / D` at general `h`**: the spin-correlation case
`F = spinProduct A`. -/
theorem correlation_eq_highTempSubsetNumerator_div_denominator
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A =
      highTempSubsetNumerator G p (spinProduct A) /
        highTempSubsetDenominator G p :=
  correlation_high_temp_expansion_general_h_subset_form G p A

/-- **Connected two-point function in general-`h` subset form (GJ §18.5/§18.7)**:
\[
\langle\sigma_i;\sigma_j\rangle_p
  = \frac{N[\sigma_{\{i,j\}}]}{D}
    - \frac{N[\sigma_{\{i\}}]}{D}\cdot\frac{N[\sigma_{\{j\}}]}{D}.
\]
The connected (truncated) two-point function — the object whose decay the
cluster expansion controls in GJ §18.7 — expressed at a general external field
through the §18.3 subset expansion of each constituent thermal average. A
finite-volume lattice Ising identity (no continuum limit).

References: GJ §18.5, pp. 313–316; §18.7, pp. 319–322. -/
theorem truncated2_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j : ι) :
    truncated2 G p i j =
      highTempSubsetNumerator G p (spinProduct {i, j}) /
          highTempSubsetDenominator G p -
        highTempSubsetNumerator G p (spinProduct {i}) /
            highTempSubsetDenominator G p *
          (highTempSubsetNumerator G p (spinProduct {j}) /
            highTempSubsetDenominator G p) := by
  unfold truncated2
  rw [correlation_eq_highTempSubsetNumerator_div_denominator G p {i, j},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {i},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {j}]

/-- **Connected three-point (Ursell) function in general-`h` subset form
(GJ §18.5/§18.7)**: the truncated three-point function with each constituent
correlation expressed through the §18.3 subset expansion at general external
field. A finite-volume lattice Ising identity (no continuum limit).

References: GJ §18.5, pp. 313–316; §18.7, pp. 319–322. -/
theorem truncated3_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) :
    truncated3 G p i j k =
      highTempSubsetNumerator G p (spinProduct {i, j, k}) /
          highTempSubsetDenominator G p
        - highTempSubsetNumerator G p (spinProduct {i}) /
            highTempSubsetDenominator G p *
          (highTempSubsetNumerator G p (spinProduct {j, k}) /
            highTempSubsetDenominator G p)
        - highTempSubsetNumerator G p (spinProduct {j}) /
            highTempSubsetDenominator G p *
          (highTempSubsetNumerator G p (spinProduct {i, k}) /
            highTempSubsetDenominator G p)
        - highTempSubsetNumerator G p (spinProduct {k}) /
            highTempSubsetDenominator G p *
          (highTempSubsetNumerator G p (spinProduct {i, j}) /
            highTempSubsetDenominator G p)
        + 2 * (highTempSubsetNumerator G p (spinProduct {i}) /
            highTempSubsetDenominator G p)
          * (highTempSubsetNumerator G p (spinProduct {j}) /
            highTempSubsetDenominator G p)
          * (highTempSubsetNumerator G p (spinProduct {k}) /
            highTempSubsetDenominator G p) := by
  unfold truncated3
  rw [correlation_eq_highTempSubsetNumerator_div_denominator G p {i, j, k},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {i},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {j, k},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {j},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {i, k},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {k},
      correlation_eq_highTempSubsetNumerator_div_denominator G p {i, j}]

end IsingModel
