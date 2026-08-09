import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d divergence of the partition function along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and along `Ambient.cubicExhaustion d`, the divergence to `atTop` of the partition
function and of its logarithm as the stage index grows. Each statement assumes the
ferromagnetic hypothesis on the parameter record and the instance `Infinite (Fin d → ℤ)`, and
nothing else.
-/

namespace IsingModel
namespace Ambient

/-- **log Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **log Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **Z → ∞ along any-Exhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop_general
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) Λ p hf

/-- **Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

end Ambient
end IsingModel
