import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms

/-!
# Concrete partition-function cubicExhaustion-Λ closed-form wrappers

Narrow child module for six ℤ^d cubicExhaustion-Λ closed-form wrappers
(Z and log Z, at `J = 0`, `β = 0`, and `zero_params` trivial slices).
Each wrapper is a thin pass-through to the corresponding ambient
`partitionFunctionΛ_{J_zero,beta_zero,zero_params}` lemma at the
`cubicExhaustion` volume.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`**:
`Z_{Λ_n}(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`**:
`Z_{Λ_n}(⟨J, h, 0⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_beta_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`**:
`Z_{Λ_n}(⟨0, 0, β⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_zero_params`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) β

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0`**:
`log Z_{Λ_n}(⟨0, h, β⟩) = |Λ_n| · log(2·cosh(β·h))` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_J_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero, Real.log_pow]

/-- **ℤ^d log_partitionFunctionΛ closed form at `β = 0`**:
`log Z_{Λ_n}(⟨J, h, 0⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_beta_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero, Real.log_pow]

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0, h = 0`**:
`log Z_{Λ_n}(⟨0, 0, β⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_zero_params`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  by rw [partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params, Real.log_pow]

end Ambient
end IsingModel
