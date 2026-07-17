import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete Lambda-layer correlation monotonicity wrappers

Narrow child module for concrete `latticeGraph` Lambda-layer correlation and
magnetization convergence / monotonicity wrappers. The theorem names are the
same as the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Lambda-layer correlation and magnetization wrappers -/

/-! ## Moved: magnetizationΛ convergent_{J,h,β} wrappers

The three wrappers
`magnetizationΛ_latticeGraph_convergent_J`,
`magnetizationΛ_latticeGraph_convergent_h`,
`magnetizationΛ_latticeGraph_convergent_beta` now live in
`LambdaCorrelationMonotonicityMagnetization.lean`. -/


/-- **ℤ^d correlationJΛ nonneg** at Λ-induced (ferromagnetic):
`0 ≤ correlationJ Λ h β B J` for `h, J ≥ 0, β > 0`. -/
theorem correlationJΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset (↑Λ : Type _))
    (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ IsingModel.correlationJ
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J :=
  IsingModel.correlationJ_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B J hJ

/-- **ℤ^d correlationJΛ ≤ 1** at Λ-induced. -/
theorem correlationJΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (B : Finset (↑Λ : Type _)) (J : ℝ) :
    IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J ≤ 1 :=
  IsingModel.correlationJ_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J

/-- **ℤ^d correlationΛ J → ∞ convergence**: for `0 ≤ h`, `0 < β`. -/
theorem correlationΛ_latticeGraph_convergent
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlationΛ β → ∞ convergence**: for `0 ≤ J`, `0 ≤ h`, the sequence
`n ↦ ⟨σ^A⟩_Λ(J, h, n+1)` converges. -/
theorem correlationΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

/-- **ℤ^d correlationΛ h → ∞ convergence**: for `0 ≤ J`, `0 < β`, the sequence
`n ↦ ⟨σ^A⟩_Λ(J, n, β)` converges. -/
theorem correlationΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ A

/-! ## Moved: correlationΛ monotone wrappers

The three `correlationΛ_latticeGraph_monotone_{h,beta,J}` wrappers
now live in `LambdaCorrelationMonotonicityMonotone.lean`. -/



end Ambient
end IsingModel
