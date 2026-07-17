import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyInfinite bridge wrappers

Narrow child module for four ℤ^d `freeEnergyInfinite_latticeGraph_*`
bridge wrappers extracted from
`PartitionFreeEnergyBoundsInfinite.lean`:

* `freeEnergyInfinite_latticeGraph_eq_of_tendsto`,
* `freeEnergyInfinite_latticeGraph_of_eventually_const`,
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto`,
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyInfinite_eq_of_tendsto` /
`freeEnergyInfinite_of_eventually_const` lemma at
`G := IsingModel.latticeGraph d` (with generic Exhaustion or
cubicExhaustion). The theorem names are unchanged from the former
`PartitionFreeEnergyBoundsInfinite` declarations.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d freeEnergyInfinite from convergence** (any-Exhaustion): if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_eq_of_tendsto
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence** (any-Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) Λ p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite from convergence**: if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto
    (d : ℕ) (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const
    (d : ℕ) (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

end Ambient

end IsingModel
