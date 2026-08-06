import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlationAlongExhaustion bound/monotone/convergent wrappers

Narrow child module for four ℤ^d
`correlationAlongExhaustion_latticeGraph_{bddBelow,bddAbove,monotone,convergent}`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `correlationAlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationAlongExhaustion` bounded below** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddBelow (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` bounded above** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` monotone** (ferromagnetic):
volume-increasing ⇒ correlation nondecreasing. -/
theorem correlationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d `correlationAlongExhaustion` existential convergence**
(ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop (nhds L) :=
  correlationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf A

end Ambient
end IsingModel
