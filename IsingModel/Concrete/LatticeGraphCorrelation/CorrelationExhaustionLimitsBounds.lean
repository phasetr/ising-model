import IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity
import IsingModel.AmbientLattice.CorrelationInfinite
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Concrete correlationAlongExhaustion bound + eventually wrappers

Narrow child module for six ℤ^d
`correlationAlongExhaustion_latticeGraph_*` bound + eventually +
cubicExhaustion `_le_one` / `_nonneg` wrappers. Each wrapper is a thin
pass-through to the corresponding ambient
`correlationAlongExhaustion_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion range is bddAbove**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually**. -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `correlationAlongExhaustion` eventually equals the lifted `correlationΛ`**
(any-Exhaustion): for any finite `A`, eventually `A ⊆ Λ.volume n` and
`correlationAlongExhaustion = correlationΛ` on the lifted set. -/
theorem correlationAlongExhaustion_latticeGraph_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ hA : A ⊆ Λ.volume n,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n =
        correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (Ambient.liftFinset A hA) :=
  correlationAlongExhaustion_eventually (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually** (any-Exhaustion). -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one
    (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationAlongExhaustion ≤ 1** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A n

/-- **ℤ^d correlationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A n


end Ambient
end IsingModel
