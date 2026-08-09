import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d partition function along an exhaustion: volume growth and positivity

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, the passage from stage `n` to stage `n + 1`: the partition function does not
decrease, and neither does its logarithm, under the ferromagnetic hypothesis on the parameter
record. Strict positivity of the partition function is stated separately and carries no
hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity**
(ferromagnetic, any-Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_volume
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          Λ p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d) Λ p n

end Ambient
end IsingModel
