import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d evenness of the partition function in the external field

Instantiates at `IsingModel.latticeGraph d` the evenness of the partition function under
negating the external field, on a fixed finite volume `Λ` and also on the stage-`n` volume of
`Ambient.cubicExhaustion d`, together with its rewriting at `|h|` and its monotonicity in `|h|`,
each of which is stated on a fixed finite volume `Λ` only. The evenness and rewriting statements
carry no hypothesis; the monotonicity statement assumes `0 ≤ J`, `0 < β` and `|h₁| ≤ |h₂|`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunctionΛ h-evenness** (any Finset):
`Z_Λ(J, -h, β) = Z_Λ(J, h, β)`. -/
theorem partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ h-evenness**:
`Z_{Λ_n}(J, -h, β) = Z_{Λ_n}(J, h, β)` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_neg_h`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n) (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h β

/-- **ℤ^d partitionFunctionΛ `|h|`-rewrite**:
`Z_Λ(J,h,β) = Z_Λ(J,|h|,β)`. Concrete specialization of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z_Λ(J,h₁,β) ≤ Z_Λ(J,h₂,β)`. Concrete specialization of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

end Ambient
end IsingModel
