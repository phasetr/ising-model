import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.PeierlsInfinite
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d complex along-exhaustion unfolding + real-complex compatibility

Narrow child module for four ℤ^d complex along-exhaustion wrappers
extracted from `PerStage.lean`:

* `partitionFunctionComplexAlongExhaustion_latticeGraph_apply`,
* `freeEnergyComplexAlongExhaustion_latticeGraph_apply`,
* `partitionFunctionComplexAlongExhaustion_at_real_latticeGraph`,
* `freeEnergyComplexAlongExhaustion_at_real_latticeGraph`.

These are foundational identities for the GJ §4.6 Thm 4.6.2
∞-volume Vitali completion at ℤ^d: the two `_apply` lemmas unfold
`partitionFunctionComplexAlongExhaustion` / `freeEnergyComplexAlongExhaustion`
on the `n`-th volume, and the two `_at_real_*` lemmas record the
real-complex compatibility identity
`Z_ℂ_{Λ_n}(↑p.J, ↑p.h, ↑p.β) = ↑(Z_ℝ_{Λ_n}(p))` (and the analogous
identity for the free energy).

Each result is a thin pass-through to the ambient
`Ambient.partitionFunctionComplexAlongExhaustion_*` /
`freeEnergyComplexAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PerStage` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunctionComplexAlongExhaustion` unfolding**:
equal to `partitionFunctionComplex` on the `n`-th volume of the
exhaustion. -/
theorem partitionFunctionComplexAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n
      = IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) J h β :=
  Ambient.partitionFunctionComplexAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d `freeEnergyComplexAlongExhaustion` unfolding**:
equal to `freeEnergyComplex` on the `n`-th volume of the exhaustion. -/
theorem freeEnergyComplexAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J h β : ℂ) (n : ℕ) :
    Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ J h β n
      = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph
            (IsingModel.latticeGraph d) (Λ.volume n)) J h β :=
  Ambient.freeEnergyComplexAlongExhaustion_apply
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d real-complex compatibility for `partitionFunction_along_exhaustion`**:
`Z_ℂ_{Λ_n}(↑p.J, ↑p.h, ↑p.β) = ↑(Z_ℝ_{Λ_n}(p))`. Foundational identity for
the Vitali completion's real-axis limit identification. -/
theorem partitionFunctionComplexAlongExhaustion_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    Ambient.partitionFunctionComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((Ambient.partitionFunctionAlongExhaustion
          (IsingModel.latticeGraph d) Λ p n : ℝ) : ℂ) :=
  Ambient.partitionFunctionComplexAlongExhaustion_at_real_eq_ofReal
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d real-complex compatibility for `freeEnergy_along_exhaustion`**:
`f_ℂ_{Λ_n}(↑p.J, ↑p.h, ↑p.β) = ↑(f_ℝ_{Λ_n}(p))`. Foundational identity
for the Vitali completion's real-axis Fekete identification. -/
theorem freeEnergyComplexAlongExhaustion_at_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n
      = ((Ambient.freeEnergyAlongExhaustion
          (IsingModel.latticeGraph d) Λ p n : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_at_real_eq_ofReal
    (IsingModel.latticeGraph d) Λ p n

end Ambient
end IsingModel
