import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d evaluation of the infinite-volume free-energy density

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and along `Ambient.cubicExhaustion d`, the evaluation of `freeEnergyInfinite` —
the `limsup` of the per-stage free-energy densities — whenever that sequence is known to
converge or to be eventually constant: the value is the limit, respectively the eventual
constant. That convergence or eventual-constancy hypothesis is the only hypothesis each
statement carries.
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
