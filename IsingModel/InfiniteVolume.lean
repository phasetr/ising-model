import IsingModel.Inequalities.GKS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Infinite volume limit

The convergence of Ising model correlation functions as the lattice
grows to infinity. The proof uses GKS-II (monotonicity in coupling
constants) and the boundedness of spin products.

## Main results

* `abs_correlation_le_one` — `|⟨σ^A⟩| ≤ 1` for the Ising model
* `abs_spinProduct_eq_one` — `|σ^A| = 1` for any configuration

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2, pp. 58–59.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boundedness of spin products (Proposition 4.2.2) -/

omit [Fintype ι] [DecidableEq ι] in
/-- The absolute value of any spin product is `1`: `|σ^A(σ)| = 1`.
Since each `σ_i ∈ {+1, -1}`, the product of `±1` values is `±1`. -/
theorem abs_spinProduct_eq_one (A : Finset ι) (σ : Config ι) :
    |spinProduct A σ| = 1 := by
  have hsq := spinProduct_sq A σ
  have h1 : |spinProduct A σ| ^ 2 = 1 := by rwa [sq_abs]
  nlinarith [abs_nonneg (spinProduct A σ),
    sq_abs (spinProduct A σ)]

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product is bounded: `|σ^A(σ)| ≤ 1`.
Immediate from `abs_spinProduct_eq_one`. -/
theorem abs_spinProduct_le_one (A : Finset ι) (σ : Config ι) :
    |spinProduct A σ| ≤ 1 :=
  le_of_eq (abs_spinProduct_eq_one A σ)

/-- **Proposition 4.2.2** (Glimm–Jaffe, p. 58):
For the Ising model, `|⟨σ^A⟩| ≤ 1` for any correlation function.

Proof: `|σ^A| = 1` for each configuration, so `|⟨σ^A⟩| ≤ ⟨|σ^A|⟩ = 1`. -/
theorem abs_correlation_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    |correlation G p A| ≤ 1 := by
  unfold correlation gibbsExpectation
  have hZ := partitionFunction_pos G p
  -- |Z⁻¹ · Σ σ^A w| ≤ Z⁻¹ · Σ |σ^A| w ≤ Z⁻¹ · Σ w = Z⁻¹ · Z = 1
  rw [abs_mul]
  calc |(partitionFunction G p)⁻¹| * |∑ σ, spinProduct A σ * boltzmannWeight G p σ|
      ≤ (partitionFunction G p)⁻¹ * ∑ σ, boltzmannWeight G p σ := by
        rw [abs_inv, abs_of_pos hZ]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
        calc |∑ σ, spinProduct A σ * boltzmannWeight G p σ|
            ≤ ∑ σ, |spinProduct A σ * boltzmannWeight G p σ| :=
              abs_sum_le_sum_abs _ _
          _ = ∑ σ, |spinProduct A σ| * boltzmannWeight G p σ := by
              congr 1; ext σ
              rw [abs_mul, abs_of_pos (boltzmannWeight_pos G p σ)]
          _ ≤ ∑ σ, 1 * boltzmannWeight G p σ := by
              apply Finset.sum_le_sum; intro σ _
              exact mul_le_mul_of_nonneg_right (abs_spinProduct_le_one A σ)
                (le_of_lt (boltzmannWeight_pos G p σ))
          _ = ∑ σ, boltzmannWeight G p σ := by simp
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hZ)

/-! ## Monotonicity in coupling constant (Proposition 4.2.1)

The correlation function `⟨σ^B⟩` is monotone increasing in the coupling
constant `J`. This follows from GKS-II:
`∂⟨σ^B⟩/∂J_A = ⟨σ^A σ^B⟩ - ⟨σ^A⟩⟨σ^B⟩ ≥ 0`.

In the discrete setting, we show that for `J₁ ≤ J₂` (with all other
parameters fixed), `⟨σ^B⟩_{J₁} ≤ ⟨σ^B⟩_{J₂}`.

The full proof requires showing that the derivative of ⟨σ^B⟩ w.r.t. J
equals the GKS-II expression. This is a calculus identity for the
Gibbs expectation, and its formalization is deferred to a subsequent step.

Reference: Glimm–Jaffe, Proposition 4.2.1, p. 58. -/

/-- The correlation function as a function of J (coupling constant),
with h and β fixed. -/
noncomputable def correlationJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) : ℝ → ℝ :=
  fun J => correlation G ⟨J, h, β⟩ B

/-- **Proposition 4.2.1** (Glimm–Jaffe, p. 58):
The correlation function is monotone increasing in the coupling constant J.

Proof (not formalized): The derivative `d/dJ ⟨σ^B⟩` equals
`β/Z² · Σ_e duplicateSum(B, {i_e,j_e})`, which is `≥ 0` by `duplicateSum_nonneg`.

Equivalently, for `J₂ = J₁ + δ`, the reweighting factor
`R(σ) = exp(βδ Σ_e edgeSpin)` gives `R · modifiedWeight` has HNC
(by `hasNonnegCorrelations_edge_site_product` with combined coupling
`K_e = β(J₁(1+t^e) + δ) ≥ 0`), and the R-weighted duplicate sum is ≥ 0.

Building blocks proved: `duplicateSum_nonneg`, `hasNonnegCorrelations_edge_site_product`,
`one_sub_spinProduct_nonneg`. The assembly requires either the calculus derivative
computation or the Fourier expansion on `{±1}^n`. -/
theorem correlation_monotone_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    Monotone (correlationJ G h β B) := by
  -- f(J) = num(J) / den(J) where
  -- num(J) = Σ_σ spinProduct B σ * exp(-β * H_J(σ))
  -- den(J) = Σ_σ exp(-β * H_J(σ)) = partitionFunction
  -- H_J(σ) = -J * Σ edgeSpin - h * Σ sign
  -- So exp(-β H_J) = exp(βJ Σ edgeSpin + βh Σ sign)
  -- Both num and den are finite sums of exp(affine in J), hence differentiable.
  -- deriv f = (num' den - num den') / den²
  -- = β/den² Σ_σ Σ_τ σ^B (S(σ) - S(τ)) w(σ) w(τ)
  -- = β/den² Σ_e duplicateSum(B, e) ≥ 0
  -- by duplicateSum_nonneg.
  -- Hence Monotone by monotone_of_deriv_nonneg.
  -- Define the exponent as a function of J and σ
  let E : ℝ → Config ι → ℝ := fun J σ =>
    -β * hamiltonian G ⟨J, h, β⟩ σ
  -- Each J ↦ exp(E J σ) is differentiable (E is affine in J)
  have hE_diff : ∀ σ, Differentiable ℝ (fun J => Real.exp (E J σ)) := by
    intro σ; apply Real.differentiable_exp.comp
    -- E J σ = -β * (-J * Σ es - h * Σ s) = βJ Σ es + βh Σ s, affine in J
    change Differentiable ℝ (fun J => -β * hamiltonian G ⟨J, h, β⟩ σ)
    unfold hamiltonian interactionEnergy externalFieldEnergy
    fun_prop
  -- den(J) = Σ exp(E J σ) is differentiable and positive
  let den : ℝ → ℝ := fun J => ∑ σ : Config ι, Real.exp (E J σ)
  have hden_diff : Differentiable ℝ den :=
    Differentiable.fun_sum (fun σ _ => hE_diff σ)
  have hden_pos : ∀ J, 0 < den J := fun J =>
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hden_ne : ∀ J, den J ≠ 0 := fun J => ne_of_gt (hden_pos J)
  -- num(J) = Σ σ^B exp(E J σ) is differentiable
  let num : ℝ → ℝ := fun J =>
    ∑ σ : Config ι, spinProduct B σ * Real.exp (E J σ)
  have hnum_diff : Differentiable ℝ num :=
    Differentiable.fun_sum (fun σ _ => (differentiable_const _).mul (hE_diff σ))
  -- f = num / den is differentiable
  have hf_eq : correlationJ G h β B = num / den := by
    ext J; simp only [correlationJ, correlation, gibbsExpectation,
      partitionFunction, boltzmannWeight, Pi.div_apply, div_eq_mul_inv]
    ring
  rw [hf_eq]
  apply monotone_of_deriv_nonneg (hnum_diff.div hden_diff hden_ne)
  intro J
  rw [deriv_div hnum_diff.differentiableAt hden_diff.differentiableAt (hden_ne J)]
  -- (num' den - num den') / den² ≥ 0 ← den² > 0 and num'den - num·den' ≥ 0
  apply div_nonneg _ (sq_nonneg _)
  -- The derivative computation and algebraic rearrangement to
  -- β Σ_e duplicateSum(B, e) ≥ 0 is deferred. The proof structure is:
  -- 1. Compute deriv(E J σ) w.r.t. J = β Σ_e edgeSpin(σ,e)
  -- 2. deriv num = Σ_σ σ^B · (β Σ es) · exp(E J σ) [chain rule + sum]
  -- 3. deriv den = Σ_σ (β Σ es) · exp(E J σ)
  -- 4. num'·den - num·den' = β Σ_e [Z·num(B△e) - num(B)·num(e)]
  --    = β Σ_e duplicateSum(B, e) ≥ 0 by duplicateSum_nonneg
  sorry

/-! ## Infinite volume convergence (Theorem 4.2.3)

For ferromagnetic Ising model with h ≥ 0, the correlation function
`⟨σ^B⟩_Λ` converges as Λ ↑ ℤ^d.

The proof combines:
- Monotonicity: `⟨σ^B⟩` increases with J (Proposition 4.2.1)
- Boundedness: `|⟨σ^B⟩| ≤ 1` (Proposition 4.2.2)
- Monotone bounded sequences converge

In the finite lattice setting, "Λ grows" means "J increases from 0 to J_max",
and the correlation function is a monotone bounded function of J.

The formalization of the lattice growth sequence and the convergence
theorem requires defining the sequence of finite volumes and relating
the correlation functions across different lattice sizes.
This is deferred to a subsequent step. -/

-- TODO: Formalize lattice growth sequence and convergence theorem
-- Key mathlib lemma: tendsto_of_monotone_of_bddAbove

end IsingModel
