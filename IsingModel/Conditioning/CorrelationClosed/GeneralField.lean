import IsingModel.Conditioning.CorrelationClosed.ClosedForm

/-!
# General external-field high-temperature correlation expansion (GJ §18.3/§18.5)

This module extends the `h = 0` closed-form correlation expansion
`correlation_high_temp_expansion_h_zero_closed` (Friedli–Velenik eq. (3.46),
Glimm–Jaffe §18.3) to a general external field `h`.

At `h = 0` the inner σ-sum collapses by parity to the even-subgraph boundary
condition `∂X = A`; at general `h` the external-field factor
`exp(β h ∑_i σ_i)` survives, so the correlation becomes the ratio of two
subset sums whose inner σ-sums carry the field weight. The shared
`cosh(βJ)^{|E|}` prefactor cancels between numerator and denominator.

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Numerator general-`h` subset expansion**: for any `A : Finset ι` and
Ising parameter `p = (J, h, β)`,
\[
\sum_\sigma \sigma_A\, W(\sigma)
  = (\cosh\beta J)^{|E|}
    \sum_{X \subseteq E} (\tanh\beta J)^{|X|}
    \sum_\sigma \sigma_A \Bigl(\prod_{e \in X} \sigma_e\Bigr)
    \exp\!\bigl(\beta h \textstyle\sum_i \sigma_i\bigr).
\]
This is the numerator counterpart of
`partitionFunction_high_temp_expansion_subset_form`: the same edge
decomposition `exp(βJ σ_e) = cosh(βJ)·(1 + tanh(βJ)·σ_e)`, subset expansion
`∏ (1 + x_e) = ∑_X ∏_{e∈X} x_e`, and `σ ↔ X` Fubini swap, but with the spin
insertion `spinProduct A σ` carried through the σ-sum. Unlike the `h = 0`
case (`sum_spinProduct_boltzmannWeight_h_zero_closed`) there is no parity
collapse: the field factor blocks the `{±1}` cancellation.

References: GJ §18.3, pp. 378–386; FV §3.7.3, eqs. (3.41)–(3.45), pp. 116–117. -/
private theorem numerator_spinProduct_high_temp_expansion_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    (∑ σ : Config ι, spinProduct A σ * boltzmannWeight G p σ)
      = Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ι,
              spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
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
  rw [show (∑ σ : Config ι, spinProduct A σ *
        (Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
          (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))))
      = Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
        ∑ σ : Config ι, spinProduct A σ *
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
  -- Step 5: distribute `spinProduct A σ` over the `X`-sum.
  rw [show (∑ σ : Config ι, spinProduct A σ *
        ((∑ X ∈ G.edgeFinset.powerset,
            Real.tanh (p.β * p.J) ^ X.card * ∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))))
      = ∑ σ : Config ι, ∑ X ∈ G.edgeFinset.powerset,
          spinProduct A σ *
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

/-- **Correlation general-`h` subset expansion (GJ §18.3/§18.5)**:
for any `A : Finset ι` and Ising parameter `p = (J, h, β)`,
\[
\langle \sigma_A \rangle_{p}
  = \frac{\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma \sigma_A (\prod_{e \in X} \sigma_e)
        \exp(\beta h \sum_i \sigma_i)}
         {\sum_{X \subseteq E} (\tanh\beta J)^{|X|}
      \sum_\sigma (\prod_{e \in X} \sigma_e)
        \exp(\beta h \sum_i \sigma_i)}.
\]
This is the general external-field counterpart of
`correlation_high_temp_expansion_h_zero_closed` (FV eq. (3.46)). The shared
`cosh(βJ)^{|E|}` prefactor of numerator and denominator cancels via
`inv_mul_cancel₀`; the identity needs only `cosh(βJ) ≠ 0` and holds with no
nonvanishing hypothesis on the denominator (both sides degenerate to `0`
when the denominator vanishes).

At `h = 0` the field factor is `1` and the inner σ-sums collapse by parity
to the even-subgraph boundary conditions of the closed `h = 0` form.

Combines `numerator_spinProduct_high_temp_expansion_subset_form` with
`partitionFunction_high_temp_expansion_subset_form`.

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
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))) := by
  unfold correlation gibbsExpectation
  rw [numerator_spinProduct_high_temp_expansion_subset_form G p A,
      partitionFunction_high_temp_expansion_subset_form G p]
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset,
      Real.tanh (p.β * p.J) ^ X.card *
        ∑ σ : Config ι,
          spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
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

end IsingModel
