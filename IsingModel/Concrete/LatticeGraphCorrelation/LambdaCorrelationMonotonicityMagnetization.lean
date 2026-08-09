import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume magnetization as a parameter grows without bound

Concrete `latticeGraph d` statements that, at a fixed vertex of a fixed finite volume, the
magnetization — the correlation of the singleton at that vertex — converges when one
parameter is sampled along the natural numbers and the others are held fixed. Growth of the
coupling assumes `0 ≤ h` and `0 < β`; growth of the external field assumes `0 ≤ J` and
`0 < β`; growth of the inverse temperature, taken shifted by one, assumes `0 ≤ J` and
`0 ≤ h`. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationΛ J → ∞ convergence**: specialisation of
`correlation_convergent` at `B = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β {i} n)
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ {i}

/-- **ℤ^d magnetizationΛ h → ∞ convergence**: specialisation of
`correlation_convergent_h` at `A = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) {i})
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ {i}

/-- **ℤ^d magnetizationΛ β → ∞ convergence**: specialisation of
`correlation_convergent_beta` at `A = {i}`. -/
theorem magnetizationΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) {i})
      Filter.atTop (nhds L) :=
  IsingModel.correlation_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh {i}

end Ambient
end IsingModel
