/- BaseVanish.lean
Narrow child module for the 4 ℤ^d trivial-slice vanish wrappers
extracted from `Base.lean` in PR #2036. Theorems:
`correlationΛ_latticeGraph_{beta_zero_vanish_of_nonempty,zero_params_vanish_of_nonempty}`,
`correlationAlongExhaustion_latticeGraph_{beta_zero_vanish,zero_params_vanish}`.
Each is a thin pass-through to the corresponding abstract `*_vanish`
lemma at `latticeGraph d`. The theorem names are unchanged from the
former `Base` declarations.
-/
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationΛ` vanishes at `β = 0`** for nonempty `A : Finset ↑Λ`. -/
theorem correlationΛ_latticeGraph_beta_zero_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_beta_zero_vanish_of_nonempty (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d `correlationΛ` vanishes at `J = h = 0`** for nonempty `A`. -/
theorem correlationΛ_latticeGraph_zero_params_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_zero_params_vanish_of_nonempty (IsingModel.latticeGraph d) Λ β A hA

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `β = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_beta_zero_vanish (IsingModel.latticeGraph d)
    Λ J h A hA n

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `J = h = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_zero_params_vanish (IsingModel.latticeGraph d)
    Λ β A hA n

end Ambient

end IsingModel
