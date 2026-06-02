import IsingModel.PhaseTransition.MagnetizationSusceptibility
import IsingModel.Conditioning.CorrelationClosed.GeneralField

/-!
# External-field response of correlations via the high-temperature expansion (GJ §17.6 / §18.3)

The Glimm–Jaffe §17.6 field-derivative (fluctuation-response) formula
\[
\frac{\partial}{\partial h}\langle\sigma_A\rangle_h
  = \beta\bigl(\langle\sigma_A M\rangle_h - \langle\sigma_A\rangle_h\langle M\rangle_h\bigr),
  \qquad M(\sigma) = \sum_i \sigma_i,
\]
combined with the §18.3 high-temperature subset expansion of thermal averages
(`gibbsExpectation_high_temp_expansion_general_h_subset_form`), expresses the
external-field response coefficient entirely in the high-temperature subset
form. Each thermal average `⟨σ_A M⟩`, `⟨σ_A⟩`, `⟨M⟩` becomes a ratio of subset
sums sharing the common denominator
`∑_{X⊆E} tanh(βJ)^{|X|} ∑_σ (∏_{e∈X} σ_e) e^{βh∑σ}`.

This connects the §5.3 / §17.6 susceptibility/response machinery with the
§18.3 cluster/high-temperature expansion.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **External-field response of `⟨σ_A⟩` in high-temperature subset form
(GJ §17.6 / §18.3)**: for any `A : Finset ι`,
\[
\frac{\partial}{\partial h}\langle\sigma_A\rangle_h
  = \beta\Bigl(\frac{N[\sigma_A M]}{D} - \frac{N[\sigma_A]}{D}\cdot\frac{N[M]}{D}\Bigr),
\]
where `N[F] = ∑_{X⊆E} tanh(βJ)^{|X|} ∑_σ F(σ)(∏_{e∈X}σ_e) e^{βh∑σ}` and
`D = N[1]`. Obtained by rewriting the three thermal averages of the GJ §17.6
fluctuation-response formula `hasDerivAt_correlation_field` through the §18.3
master subset expansion `gibbsExpectation_high_temp_expansion_general_h_subset_form`.

References: GJ §17.6, pp. 348–351; §18.3, pp. 378–386. -/
theorem hasDerivAt_correlation_field_high_temp_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    HasDerivAt (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A)
      (β * (
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (spinProduct A σ * totalMagnetization σ) *
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))) -
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))) *
        ((∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              totalMagnetization σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i)))))) h := by
  have h0 := hasDerivAt_correlation_field G J h β A
  rw [gibbsExpectation_high_temp_expansion_general_h_subset_form G
        (⟨J, h, β⟩ : IsingParams ℝ) (fun σ => spinProduct A σ * totalMagnetization σ),
      correlation_high_temp_expansion_general_h_subset_form G
        (⟨J, h, β⟩ : IsingParams ℝ) A,
      gibbsExpectation_high_temp_expansion_general_h_subset_form G
        (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization] at h0
  exact h0

/-- **External-field response of the magnetization `⟨σ_i⟩` in high-temperature
subset form (GJ §17.6 / §18.3)**: the local field susceptibility
`∂⟨σ_i⟩/∂h` in the §18.3 subset expansion, the `A = {i}` specialisation of
`hasDerivAt_correlation_field_high_temp_subset_form` via
`magnetization G p i = correlation G p {i}`.

References: GJ §17.6, pp. 348–351; §18.3, pp. 378–386. -/
theorem hasDerivAt_magnetization_field_high_temp_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun h' => magnetization G (⟨J, h', β⟩ : IsingParams ℝ) i)
      (β * (
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (spinProduct {i} σ * totalMagnetization σ) *
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j))) -
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              spinProduct {i} σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j))) *
        ((∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              totalMagnetization σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j))) /
        (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (β * h * ∑ j : ι, Spin.sign ℝ (σ j)))))) h := by
  unfold magnetization
  exact hasDerivAt_correlation_field_high_temp_subset_form G J h β {i}

end IsingModel
