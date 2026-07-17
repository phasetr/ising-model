import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d cubicExhaustion partitionFunctionAlongEx volume + pos wrappers

Narrow child module for three ℤ^d
`partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_*`
wrappers extracted from `PartitionExhaustionBounds.lean`:

* `log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume`,
* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume`,
* `partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos`.

Each result instantiates the corresponding generic
`partitionFunctionAlongExhaustion_*` lemma at the concrete cubic
exhaustion. The theorem names are unchanged from the former
`PartitionExhaustionBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic):
`partitionFunctionAlongExhaustion` at stage `n+1` is ≥ stage `n`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

end Ambient
end IsingModel
