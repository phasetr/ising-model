import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete partition-function cubicExhaustion-Λ closed-form wrappers

Instantiates the Λ-level partition-function closed forms on the degenerate parameter slices
at `IsingModel.latticeGraph d` over the `cubicExhaustion` volumes, so a ℤ^d caller can
evaluate a cubic box directly.
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

end Ambient
end IsingModel
