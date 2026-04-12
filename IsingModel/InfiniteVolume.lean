import IsingModel.Inequalities.GKS

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
The correlation function `⟨σ^B⟩` is monotone increasing in `J`.

Proof: `d/dJ ⟨σ^B⟩ = β Σ_e (⟨edgeSpin(e) · σ^B⟩ - ⟨edgeSpin(e)⟩⟨σ^B⟩) ≥ 0`
by GKS-II applied to each edge term.

The full formalization requires:
1. Differentiability of correlationJ (finite sum of exp, quotient rule)
2. Derivative computation (product rule + chain rule for exp)
3. GKS-II applied to each edge term
4. monotone_of_deriv_nonneg

This is deferred pending the derivative computation. -/
theorem correlation_monotone_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    Monotone (correlationJ G h β B) := by
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
