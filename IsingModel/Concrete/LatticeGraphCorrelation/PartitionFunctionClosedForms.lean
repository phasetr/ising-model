import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d closed forms for the partition function at trivial parameter slices

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the closed forms
taken by the partition function where the interaction degenerates: `(2 * cosh (β * h)) ^ |Λ|`
at zero coupling, and `2 ^ |Λ|` at zero inverse temperature and at zero coupling with zero
field. The vanishing parameters are substituted literally, so no statement here carries a
hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`** (any Finset):
`Z_Λ(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Λ.card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`** (any Finset):
`Z_Λ(⟨J, h, 0⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`** (any Finset):
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. -/
theorem partitionFunctionΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d) Λ β

end Ambient
end IsingModel
