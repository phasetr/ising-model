import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CauchyDerivativeBridge
import IsingModel.ComplexAnalyticity.Correlation

/-!
# Derivative-increment bridge from a complex circle bound (Issue #3026)

Assembles the Cauchy-estimate derivative bridge (`dist_deriv_le_of_complex_extension`)
with the complex correlation extension (`correlationComplex`, `correlation_ofReal_eq_*`,
`correlationComplex_diffContOnCl_beta`) into a single conditional reduction:

If two finite-volume correlations have complex extensions that are nonvanishing on a
common closed disc `closedBall β R` and whose difference is bounded by `B` on the
boundary circle, then their real β-derivatives differ by at most `B / R`:
`dist(∂_β ⟨σ^A⟩_{G₁}, ∂_β ⟨σ^A⟩_{G₂}) ≤ B / R`.

This reduces the GJ §17.5 Lemma 17.5.2 capstone `hincr` (the β-derivative increment over
consecutive cubic-exhaustion stages) to its single remaining hard core: a **complex
boundary-circle bound** `B` on the value increment `⟨σ^A⟩_{G₁} − ⟨σ^A⟩_{G₂}` (a
complex/Lee-Yang-region Simon-Lieb estimate).

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311–312.
-/

namespace IsingModel
namespace Ambient

open Complex Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Derivative-increment bridge from a complex circle bound** (Issue #3026). For two
finite-volume Ising correlations on graphs `G₁, G₂` at real parameters `J, h` and a real
inverse temperature `β`, if both complex partition functions are nonzero on the closed
disc `closedBall β R` (`R > 0`) and the complex correlation difference is bounded by `B`
on the boundary circle `sphere β R`, then the real β-derivatives satisfy
`dist(∂_β ⟨σ^A⟩_{G₁}, ∂_β ⟨σ^A⟩_{G₂}) ≤ B / R`.

The complex extensions `correlationComplex` are `DiffContOnCl` on the disc
(`correlationComplex_diffContOnCl_beta`), their difference too (`DiffContOnCl.sub`), the
real correlations are their real parts (`correlation_ofReal_eq_correlationComplex`), and
the conclusion is the capstone-shaped Cauchy bridge `dist_deriv_le_of_complex_extension`.
-/
theorem dist_deriv_correlation_le_of_complex_circle_bound (G₁ G₂ : SimpleGraph ι)
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (A : Finset ι) (J h β : ℝ) {R B : ℝ}
    (hR : 0 < R)
    (hZ1 : ∀ z ∈ closedBall (β : ℂ) R, partitionFunctionComplex G₁ (J : ℂ) (h : ℂ) z ≠ 0)
    (hZ2 : ∀ z ∈ closedBall (β : ℂ) R, partitionFunctionComplex G₂ (J : ℂ) (h : ℂ) z ≠ 0)
    (hB : ∀ z ∈ sphere (β : ℂ) R,
      ‖correlationComplex G₁ A (J : ℂ) (h : ℂ) z - correlationComplex G₂ A (J : ℂ) (h : ℂ) z‖
        ≤ B) :
    dist (deriv (fun β' => correlation G₁ (⟨J, h, β'⟩ : IsingParams ℝ) A) β)
        (deriv (fun β' => correlation G₂ (⟨J, h, β'⟩ : IsingParams ℝ) A) β) ≤ B / R := by
  -- Real-part agreement of each complex extension with the real correlation.
  have hre₁ : ∀ x : ℝ, (correlationComplex G₁ A (J : ℂ) (h : ℂ) (x : ℂ)).re
      = correlation G₁ (⟨J, h, x⟩ : IsingParams ℝ) A := by
    intro x
    rw [← correlation_ofReal_eq_correlationComplex G₁ (⟨J, h, x⟩ : IsingParams ℝ) A,
      Complex.ofReal_re]
  have hre₂ : ∀ x : ℝ, (correlationComplex G₂ A (J : ℂ) (h : ℂ) (x : ℂ)).re
      = correlation G₂ (⟨J, h, x⟩ : IsingParams ℝ) A := by
    intro x
    rw [← correlation_ofReal_eq_correlationComplex G₂ (⟨J, h, x⟩ : IsingParams ℝ) A,
      Complex.ofReal_re]
  -- Differentiability of the real correlations at `β`, via the complex extension.
  have hdiff₁ : DifferentiableAt ℝ
      (fun β' => correlation G₁ (⟨J, h, β'⟩ : IsingParams ℝ) A) β := by
    have he : HasDerivAt (fun z => correlationComplex G₁ A (J : ℂ) (h : ℂ) z)
        (deriv (fun z => correlationComplex G₁ A (J : ℂ) (h : ℂ) z) (β : ℂ)) (β : ℂ) :=
      (correlationComplex_analyticAt_beta G₁ A (J : ℂ) (h : ℂ) (β : ℂ)
        (hZ1 (β : ℂ) (mem_closedBall_self hR.le))).differentiableAt.hasDerivAt
    rw [show (fun β' => correlation G₁ (⟨J, h, β'⟩ : IsingParams ℝ) A)
        = (fun x : ℝ => (correlationComplex G₁ A (J : ℂ) (h : ℂ) (x : ℂ)).re) from
        (funext hre₁).symm]
    exact he.real_of_complex.differentiableAt
  have hdiff₂ : DifferentiableAt ℝ
      (fun β' => correlation G₂ (⟨J, h, β'⟩ : IsingParams ℝ) A) β := by
    have he : HasDerivAt (fun z => correlationComplex G₂ A (J : ℂ) (h : ℂ) z)
        (deriv (fun z => correlationComplex G₂ A (J : ℂ) (h : ℂ) z) (β : ℂ)) (β : ℂ) :=
      (correlationComplex_analyticAt_beta G₂ A (J : ℂ) (h : ℂ) (β : ℂ)
        (hZ2 (β : ℂ) (mem_closedBall_self hR.le))).differentiableAt.hasDerivAt
    rw [show (fun β' => correlation G₂ (⟨J, h, β'⟩ : IsingParams ℝ) A)
        = (fun x : ℝ => (correlationComplex G₂ A (J : ℂ) (h : ℂ) (x : ℂ)).re) from
        (funext hre₂).symm]
    exact he.real_of_complex.differentiableAt
  -- `DiffContOnCl` of each extension and of their difference.
  have hd : DiffContOnCl ℂ
      (fun z => correlationComplex G₁ A (J : ℂ) (h : ℂ) z
        - correlationComplex G₂ A (J : ℂ) (h : ℂ) z) (ball (β : ℂ) R) :=
    (correlationComplex_diffContOnCl_beta G₁ A (J : ℂ) (h : ℂ) (β : ℂ) hR hZ1).sub
      (correlationComplex_diffContOnCl_beta G₂ A (J : ℂ) (h : ℂ) (β : ℂ) hR hZ2)
  -- Real-part agreement of the difference.
  have hext : ∀ x : ℝ, (correlationComplex G₁ A (J : ℂ) (h : ℂ) (x : ℂ)
        - correlationComplex G₂ A (J : ℂ) (h : ℂ) (x : ℂ)).re
      = correlation G₁ (⟨J, h, x⟩ : IsingParams ℝ) A
        - correlation G₂ (⟨J, h, x⟩ : IsingParams ℝ) A := by
    intro x; rw [Complex.sub_re, hre₁, hre₂]
  exact dist_deriv_le_of_complex_extension hR hdiff₁ hdiff₂ hext hd hB

end Ambient
end IsingModel
