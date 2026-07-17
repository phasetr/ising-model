import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d freeEnergyInfinite bridge / BED upper-bound wrappers

Narrow child module for the 6 ℤ^d `freeEnergyInfinite_latticeGraph_*`
bridge wrappers (`eq_of_tendsto`, `of_eventually_const`,
`cubicExhaustion_eq_of_tendsto`, `cubicExhaustion_of_eventually_const`,
`le_uniform_upper_bound`, `cubicExhaustion_le_uniform_upper_bound`)
extracted from `PartitionFreeEnergyBounds.lean` in PR #2057. Each is a
thin pass-through to the corresponding `freeEnergyInfinite_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from the
former `PartitionFreeEnergyBounds` declarations.
-/

namespace IsingModel

namespace Ambient

/-! ## Infinite-volume free-energy bridges and BED bounds -/

/-! ## Moved: freeEnergyInfinite bridge wrappers

The four wrappers
`freeEnergyInfinite_latticeGraph_eq_of_tendsto`,
`freeEnergyInfinite_latticeGraph_of_eventually_const`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const`
now live in `PartitionFreeEnergyBoundsInfiniteBridge.lean`. -/


/-- **ℤ^d freeEnergyInfinite uniform upper bound via caller-supplied BED**
(any-Exhaustion): `freeEnergyInfinite ≤ log 2 + |β|·(|J|·c + |h|)`. -/
theorem freeEnergyInfinite_latticeGraph_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) :=
  freeEnergyInfinite_le_uniform_upper_bound
    (IsingModel.latticeGraph d) Λ p hf hc

/-- **ℤ^d freeEnergyInfinite uniform upper bound via BED**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyInfinite_le_uniform_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

end Ambient

end IsingModel
