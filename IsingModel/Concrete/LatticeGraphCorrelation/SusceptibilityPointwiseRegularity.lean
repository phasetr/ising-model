import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d regularity of the along-exhaustion susceptibility in the coupling

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the susceptibility of that stage is continuous, and
differentiable over `ℝ`, as a function of the coupling on the whole line, with the external
field and the inverse temperature held fixed and unrestricted. No statement here carries a
hypothesis or takes an instance argument.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **susceptibilityAlongExhaustion Continuous in J**. -/
theorem susceptibilityAlongExhaustion_continuous_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (h β : ℝ) (n : ℕ) :
    Continuous
      (fun J' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_J_gen
    (IsingModel.latticeGraph d) Λ h β i n

/-- **susceptibilityAlongExhaustion Differentiable in J**. -/
theorem susceptibilityAlongExhaustion_differentiable_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (i : Fin d → ℤ) (h β : ℝ) (n : ℕ) :
    Differentiable ℝ
      (fun J' => susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J', h, β⟩ : IsingParams ℝ) i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_J_gen
    (IsingModel.latticeGraph d) Λ h β i n

end Ambient
end IsingModel
