import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d closed forms for the partition function at zero coupling, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the closed forms taken by the partition function and by
its logarithm at zero coupling with zero field, `2 ^ |Λ_n|` and `|Λ_n| * log 2`, and at zero
coupling with an arbitrary field, `(2 * cosh (β * h)) ^ |Λ_n|` and
`|Λ_n| * log (2 * cosh (β * h))`. The vanishing parameters are substituted literally, so no
statement here carries a hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage** (any-Exhaustion):
`= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0** (any-Exhaustion):
`= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage** (any-Exhaustion):
`= (2·cosh(β·h))^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0** (any-Exhaustion):
`= |Λ_n|·log(2·cosh(β·h))`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero
    (IsingModel.latticeGraph d) Λ h β n

end Ambient
end IsingModel
