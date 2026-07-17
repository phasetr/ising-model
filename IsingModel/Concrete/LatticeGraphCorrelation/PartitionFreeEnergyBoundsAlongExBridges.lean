import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d freeEnergyAlongExhaustion bridge / per-stage bound wrappers

Narrow child module for the 8 ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_*` BddAbove / per-stage
upper-bound / per-stage `log 2` and `log(2 cosh)` lower-bound /
ferromagnetic per-stage nonneg wrappers
(`BddAbove_*_range`, `BddAbove_*_cubicExhaustion`,
`*_cubicExhaustion_le_uniform_upper_bound`,
`*_cubicExhaustion_ge_log_two`, `*_cubicExhaustion_ge_log_two_cosh`,
`*_ge_log_two`, `*_ge_log_two_cosh`, `*_nonneg`) extracted from
`PartitionFreeEnergyBounds.lean` in PR #2058. Each is a thin
pass-through to the corresponding ambient
`freeEnergyAlongExhaustion_*` lemma at `IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`PartitionFreeEnergyBounds` declarations.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`** (any-Exhaustion,
caller-supplied BED). -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_range
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d) Λ p hBED

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`**: via BED c=d. -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion
    (d : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)

/-- **ℤ^d per-stage freeEnergyAlongExhaustion upper bound** using BED c = d. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyAlongExhaustion_le_uniform_upper_bound
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p
    (c := (d : ℝ)) ?_ n hne
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-! ## Moved: freeEnergyAlongEx ge_log_two wrappers

The four wrappers
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two`,
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two_cosh`,
`freeEnergyAlongExhaustion_latticeGraph_ge_log_two`,
`freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh` now live in
`PartitionFreeEnergyBoundsAlongExBridgesLogTwo.lean`. -/

/-- **ℤ^d per-stage `0 ≤ f_n`** (ferromagnetic, nonempty stage, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

end Ambient

end IsingModel
