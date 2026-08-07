import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete ℤ^d AlongExhaustion partition / log-partition bounds

Instantiates the uniform lower bounds on the along-exhaustion partition function and its
logarithm at `IsingModel.latticeGraph d`, the positivity input the ℤ^d free-energy limit
arguments need at every stage.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic, any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log Z_n ≥ 0** (ferromagnetic, any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion ≥ 0** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

end Ambient

end IsingModel
