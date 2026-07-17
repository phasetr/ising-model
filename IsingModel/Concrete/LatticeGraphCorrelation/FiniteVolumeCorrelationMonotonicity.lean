import IsingModel.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume correlation monotonicity wrappers

Narrow child module for direct concrete `latticeGraph` finite-volume HNC,
Gibbs-expectation, and correlation monotonicity/convergence wrappers. The
theorem names are the same as the former declarations, but callers can
now avoid importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume expectation and correlation monotonicity wrappers -/

/-- **ℤ^d cov_hnc_boltzmann_nonneg direct** (Λ-induced, ferromagnetic):
covariance bound for HNC `f` with Boltzmann weight. -/
theorem cov_hnc_boltzmann_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hferm : Ferromagnetic p)
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hf : IsingModel.HasNonnegCorrelations f) (B : Finset (↑Λ : Type _)) :
    0 ≤ (∑ σ, IsingModel.spinProduct B σ * f σ
            * IsingModel.boltzmannWeight
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) -
      (∑ σ, IsingModel.spinProduct B σ *
          IsingModel.boltzmannWeight
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, f σ * IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) :=
  IsingModel.cov_hnc_boltzmann_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hferm f hf B

/-- **ℤ^d gibbsExpectation as ratio** at Λ-induced:
`⟨F⟩ = Z⁻¹ · numerator(F)`. -/
theorem gibbsExpectation_eq_div_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ) :
    IsingModel.gibbsExpectation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F
      = (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p)⁻¹
          * IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_eq_div
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F

/-- **ℤ^d gibbsExpectation nonneg from numerator nonneg** at Λ-induced. -/
theorem gibbsExpectation_nonneg_of_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hnum : 0 ≤ IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F) :
    0 ≤ IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_nonneg_of_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F hnum

/-! ## Moved: correlation_monotone_{J,h,β} wrappers

The three wrappers
`correlation_monotone_J_latticeGraph`,
`correlation_monotone_h_latticeGraph`,
`correlation_monotone_beta_latticeGraph` now live in
`FiniteVolumeCorrelationMonotonicityMonotone.lean`. -/


/-- **ℤ^d correlationJ_nonneg direct** (Λ-induced, ferromagnetic): for
`h ≥ 0`, `β > 0`, and `J ≥ 0`, `0 ≤ correlationJ (inducedGraph … Λ) h β B J`.
Thin pass-through of `IsingModel.correlationJ_nonneg`; GJ §4.2 Prop 4.2.1
slice at `correlationJ` (GKS-I). -/
theorem correlationJ_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ IsingModel.correlationJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J :=
  IsingModel.correlationJ_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B J hJ

/-- **ℤ^d correlationJ_le_one direct** (Λ-induced): for every `J`,
`correlationJ (inducedGraph … Λ) h β B J ≤ 1`. Thin pass-through of
`IsingModel.correlationJ_le_one` (unconditional upper bound). -/
theorem correlationJ_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (B : Finset (↑Λ : Type _)) (J : ℝ) :
    IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J ≤ 1 :=
  IsingModel.correlationJ_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J

/-! ## Moved: correlation_convergent_* wrappers

The three `correlation_convergent_latticeGraph`,
`correlation_convergent_h_latticeGraph`,
`correlation_convergent_beta_latticeGraph` wrappers now live in
`FiniteVolumeCorrelationMonotonicityConvergent.lean`. -/



end Ambient
end IsingModel
