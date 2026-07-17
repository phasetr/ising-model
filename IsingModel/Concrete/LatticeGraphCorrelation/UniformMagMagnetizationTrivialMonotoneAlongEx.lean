import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `magnetizationAlongExhaustion_latticeGraph_monotone_*` wrappers

Narrow child module for three ℤ^d
`magnetizationAlongExhaustion_latticeGraph_monotone_*` wrappers
extracted from `UniformMagMagnetizationTrivialMonotone.lean`:

* `magnetizationAlongExhaustion_latticeGraph_monotone_h`,
* `magnetizationAlongExhaustion_latticeGraph_monotone_beta`,
* `magnetizationAlongExhaustion_latticeGraph_monotone_J`.

Each result is a thin pass-through of the ambient
`Ambient.magnetizationAlongExhaustion_monotone_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagMagnetizationTrivialMonotone` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationAlongExhaustion h-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ i hh₁ hh₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion β-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh i hβ₁ hβ₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion J-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ i hJ₁ hJ₁₂ n


end Ambient
end IsingModel
