import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlationAlongExhaustion monotonicity wrappers

Narrow child module for three ℤ^d
`correlationAlongExhaustion_latticeGraph_monotone_{J,h,beta}` wrappers,
each a thin pass-through to the corresponding ambient
`correlationAlongExhaustion_monotone_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion J-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ A hJ₁ hJ₁₂ n

/-- **ℤ^d correlationAlongExhaustion h-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ A hh₁ hh₁₂ n

/-- **ℤ^d correlationAlongExhaustion β-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh A hβ₁ hβ₁₂ n

end Ambient
end IsingModel
