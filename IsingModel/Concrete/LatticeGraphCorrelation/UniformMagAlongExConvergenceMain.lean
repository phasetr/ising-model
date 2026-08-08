import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d convergence of `magnetizationAlongExhaustion` to `magnetizationInfinite`

Records, for `Ferromagnetic` parameters throughout, that the ℤ^d stagewise single-site
magnetization is monotone in the stage index, that it converges, and that its limit is
the infinite-volume magnetization.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationAlongExhaustion → magnetizationInfinite** (ferromagnetic):
Concrete specialization of `tendsto_magnetizationAlongExhaustion_magnetizationInfinite`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (magnetizationInfinite (IsingModel.latticeGraph d) Λ p i)) :=
  tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d existential convergence of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    ∃ L : ℝ, Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop (nhds L) :=
  magnetizationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d stage-index monotonicity of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Monotone (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i) :=
  magnetizationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf i

end Ambient

end IsingModel
