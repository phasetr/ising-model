import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `magnetizationAlongExhaustion` tendsto / convergent / monotone wrappers

Narrow child module for three ℤ^d
`magnetizationAlongExhaustion_latticeGraph_*` wrappers extracted from
`UniformMagAlongExConvergence.lean`:

* `tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph`,
* `magnetizationAlongExhaustion_latticeGraph_convergent`,
* `magnetizationAlongExhaustion_latticeGraph_monotone`.

Each result is a thin pass-through of the corresponding ambient
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `UniformMagAlongExConvergence` declarations.
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
