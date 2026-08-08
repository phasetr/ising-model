import IsingModel.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Convergence of finite-volume correlations along integer parameter sequences in ℤ^d

Records that on the subgraph induced by the nearest-neighbor lattice graph on a finite
`Λ ⊆ ℤ^d` the correlation of a fixed spin product converges as one parameter runs to
infinity through the natural numbers with the other two held fixed: along the coupling,
along the external field, and along the inverse temperature, the last taken along `n + 1`
so that the sequence stays strictly positive. Each statement assumes nonnegativity of the
two parameters held fixed, strengthened to strict positivity when the inverse temperature
is one of them. The limit comes from the monotone-and-bounded route of Glimm–Jaffe's
Theorem 4.2.3, p. 59, taken here in a parameter direction at fixed `Λ` rather than in the
volume direction.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlation_convergent direct** (Λ-induced, ferromagnetic):
for `h ≥ 0`, `β > 0`, the sequence `n ↦ ⟨σ^B⟩_{(J=n, h, β)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent`;
GJ §4.2 Thm 4.2.3 (J → ∞ along ℕ). -/
theorem correlation_convergent_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B

/-- **ℤ^d correlation_convergent_h direct** (Λ-induced, ferromagnetic):
for `J ≥ 0`, `β > 0`, the sequence `n ↦ ⟨σ^A⟩_{(J, n, β)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent_h`. -/
theorem correlation_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ A

/-- **ℤ^d correlation_convergent_beta direct** (Λ-induced, ferromagnetic):
for `J ≥ 0`, `h ≥ 0`, the sequence `n ↦ ⟨σ^A⟩_{(J, h, n+1)}` converges as
`n → ∞`. Thin pass-through of `IsingModel.correlation_convergent_beta`. -/
theorem correlation_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (A : Finset (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ A)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh A

end Ambient
end IsingModel
