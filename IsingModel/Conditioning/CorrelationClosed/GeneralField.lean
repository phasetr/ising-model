import IsingModel.Conditioning.CorrelationClosed.ClosedForm

/-!
# General external-field high-temperature expansion of thermal averages (GJ §18.3/§18.5)

This module gives the general external-field (`h ≠ 0`) high-temperature
expansion of arbitrary Gibbs expectations, generalising the `h = 0`
closed-form correlation expansion `correlation_high_temp_expansion_h_zero_closed`
(Friedli–Velenik eq. (3.46), Glimm–Jaffe §18.3).

For an arbitrary observable `F : Config ι → ℝ` the Gibbs expectation is the
ratio of two subset sums whose inner σ-sums carry the external-field weight
`exp(β h ∑_i σ_i)`:
\[
\langle F \rangle_p
  = \frac{\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma F(\sigma) (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}
         {\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}.
\]
The shared `cosh(βJ)^{|E|}` prefactor of numerator and denominator cancels.
At `h = 0` the inner σ-sum collapses by parity (the even-subgraph boundary
condition `∂X = A` for `F = σ_A`); at general `h` the field factor survives.
The spin-correlation case `F = spinProduct A` and the magnetization case
`F = spinProduct {i}` are immediate corollaries.

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Numerator general-`h` subset expansion for an arbitrary observable**:
for any `F : Config ι → ℝ` and Ising parameter `p = (J, h, β)`,
\[
\sum_\sigma F(\sigma)\, W(\sigma)
  = (\cosh\beta J)^{|E|}
    \sum_{X \subseteq E} (\tanh\beta J)^{|X|}
    \sum_\sigma F(\sigma) \Bigl(\prod_{e \in X} \sigma_e\Bigr)
    \exp\!\bigl(\beta h \textstyle\sum_i \sigma_i\bigr).
\]
The observable counterpart of `partitionFunction_high_temp_expansion_subset_form`
(the special case `F = 1`): the same edge decomposition
`exp(βJ σ_e) = cosh(βJ)·(1 + tanh(βJ)·σ_e)`, subset expansion
`∏ (1 + x_e) = ∑_X ∏_{e∈X} x_e`, and `σ ↔ X` Fubini swap, but with the
observable factor `F σ` carried through the σ-sum. Unlike the `h = 0` case
(`sum_spinProduct_boltzmannWeight_h_zero_closed`) there is no parity collapse:
the field factor blocks the `{±1}` cancellation.

References: GJ §18.3, pp. 378–386; FV §3.7.3, eqs. (3.41)–(3.45), pp. 116–117. -/
theorem numerator_observable_high_temp_expansion_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    (∑ σ : Config ι, F σ * boltzmannWeight G p σ)
      = Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ι,
              F σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
  -- Step 1: per-configuration Boltzmann-weight decomposition (general `h`),
  -- mirroring `partitionFunction_high_temp_expansion`.
  have hboltz : ∀ σ : Config ι,
      boltzmannWeight G p σ
        = Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
            (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    have hrewrite :
        -p.β *
            (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
          = (∑ e ∈ G.edgeFinset, p.β * p.J * edgeSpin σ e)
            + p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i) := by
      rw [show
          -p.β *
              (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
                + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
            = (p.β * p.J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e)
              + p.β * p.h * (∑ i : ι, Spin.sign ℝ (σ i)) from by ring,
          Finset.mul_sum]
    rw [hrewrite, Real.exp_add, Real.exp_sum]
    have hedge_decomp : ∀ e ∈ G.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin σ e) =
          Real.cosh (p.β * p.J) * (1 + Real.tanh (p.β * p.J) * edgeSpin σ e) := by
      intro e _
      rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
      have hcosh_ne : Real.cosh (p.β * p.J) ≠ 0 := (Real.cosh_pos _).ne'
      field_simp
    rw [Finset.prod_congr rfl hedge_decomp, Finset.prod_mul_distrib,
        Finset.prod_const]
  simp_rw [hboltz]
  -- Step 2: pull `cosh(βJ)^{|E|}` out of the σ-sum.
  rw [show (∑ σ : Config ι, F σ *
        (Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
          (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))))
      = Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
        ∑ σ : Config ι, F σ *
          ((∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)]
  congr 1
  -- Step 3: subset expansion of the edge product.
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (p.β * p.J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Step 4: pull `tanh(βJ)^{|X|}` out of each edge sub-product.
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (p.β * p.J) * edgeSpin σ e))
        = Real.tanh (p.β * p.J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Step 5: distribute `F σ` over the `X`-sum.
  rw [show (∑ σ : Config ι, F σ *
        ((∑ X ∈ G.edgeFinset.powerset,
            Real.tanh (p.β * p.J) ^ X.card * ∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))))
      = ∑ σ : Config ι, ∑ X ∈ G.edgeFinset.powerset,
          F σ *
            (Real.tanh (p.β * p.J) ^ X.card *
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]]
  -- Step 6: swap σ ↔ X and pull `tanh(βJ)^{|X|}` out of the σ-sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

/-- **Gibbs-expectation general-`h` subset expansion (GJ §18.3/§18.5)**:
for any observable `F : Config ι → ℝ` and Ising parameter `p = (J, h, β)`,
\[
\langle F \rangle_p =
  \frac{\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma F(\sigma) (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}
       {\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}.
\]
The master high-temperature representation of thermal averages: the
spin-correlation `⟨σ_A⟩` (`F = spinProduct A`) and the magnetization
`⟨σ_i⟩` (`F = spinProduct {i}`) are immediate specialisations.

The shared `cosh(βJ)^{|E|}` prefactor cancels via `inv_mul_cancel₀`; the
identity needs only `cosh(βJ) ≠ 0` and holds with no nonvanishing hypothesis
on the denominator (both sides degenerate to `0` when it vanishes).

Combines `numerator_observable_high_temp_expansion_subset_form` with
`partitionFunction_high_temp_expansion_subset_form` (the `F = 1` case).

References: GJ §18.3, pp. 378–386; FV §3.7.3, eqs. (3.41)–(3.46), pp. 116–117. -/
theorem gibbsExpectation_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    gibbsExpectation G p F =
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ι,
            F σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) /
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ι,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) := by
  unfold gibbsExpectation
  rw [numerator_observable_high_temp_expansion_subset_form G p F,
      partitionFunction_high_temp_expansion_subset_form G p]
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset,
      Real.tanh (p.β * p.J) ^ X.card *
        ∑ σ : Config ι,
          F σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) with hN_sub
  set Z_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset,
      Real.tanh (p.β * p.J) ^ X.card *
        ∑ σ : Config ι,
          (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) with hZ_sub
  -- Goal: (cosh^{|E|} · Z_sub)⁻¹ · (cosh^{|E|} · N_sub) = N_sub / Z_sub.
  -- The `cosh^{|E|}` factor cancels; no `Z_sub ≠ 0` hypothesis is needed.
  have hcosh_ne : Real.cosh (p.β * p.J) ^ G.edgeFinset.card ≠ 0 :=
    (pow_pos (Real.cosh_pos _) _).ne'
  rw [mul_inv, div_eq_mul_inv,
      show (Real.cosh (p.β * p.J) ^ G.edgeFinset.card)⁻¹ * Z_sub⁻¹ *
          (Real.cosh (p.β * p.J) ^ G.edgeFinset.card * N_sub)
        = (Real.cosh (p.β * p.J) ^ G.edgeFinset.card)⁻¹ *
            Real.cosh (p.β * p.J) ^ G.edgeFinset.card * (N_sub * Z_sub⁻¹) from by ring,
      inv_mul_cancel₀ hcosh_ne, one_mul]

/-- **Correlation general-`h` subset expansion (GJ §18.3/§18.5)**:
for any `A : Finset ι` and Ising parameter `p = (J, h, β)`,
\[
\langle \sigma_A \rangle_{p}
  = \frac{\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma \sigma_A (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}
         {\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e) e^{\beta h \sum_i \sigma_i}}.
\]
The general external-field counterpart of
`correlation_high_temp_expansion_h_zero_closed` (FV eq. (3.46)). Immediate
specialisation of `gibbsExpectation_high_temp_expansion_general_h_subset_form`
to the observable `F = spinProduct A`, since
`correlation G p A = gibbsExpectation G p (spinProduct A)`.

At `h = 0` the field factor is `1` and the inner σ-sums collapse by parity
to the even-subgraph boundary conditions of the closed `h = 0` form.

References: GJ §18.3, pp. 378–386; FV §3.7.3, eqs. (3.41)–(3.46), pp. 116–117. -/
theorem correlation_high_temp_expansion_general_h_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A =
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ι,
            spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) /
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ι,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) :=
  gibbsExpectation_high_temp_expansion_general_h_subset_form G p (spinProduct A)

end IsingModel
