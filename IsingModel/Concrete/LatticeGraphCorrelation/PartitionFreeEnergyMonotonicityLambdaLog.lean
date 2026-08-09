import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d parameter monotonicity of the log partition function on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the monotonicity of
the logarithm of the partition function in each parameter of the record `⟨J, h, β⟩`
separately. In each statement the frozen parameters carry their ferromagnetic signs —
nonnegative coupling and field, strictly positive inverse temperature — the varying parameter
starts from a nonnegative value, strictly positive in the case of the inverse temperature, and
`Λ` is not assumed nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d log_partitionFunctionΛ J-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d log_partitionFunctionΛ h-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d log_partitionFunctionΛ β-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

end Ambient
end IsingModel
