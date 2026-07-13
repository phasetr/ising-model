import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag

/-!
# ℤ^d `uniformMagnetization_monotone_*` wrappers

Narrow child module for three ℤ^d `uniformMagnetization_monotone_*`
parameter-direction monotonicity wrappers extracted from
`SiteIndepMagTrivialSlice.lean`:

* `uniformMagnetization_monotone_J`,
* `uniformMagnetization_monotone_h`,
* `uniformMagnetization_monotone_beta`.

Each result is a thin pass-through of the ambient
`Ambient.magnetizationInfinite_monotone_*` lemma at
`G := IsingModel.latticeGraph d` and `Ambient.cubicExhaustion d` at
site `0`. The theorem names are unchanged from the former
`SiteIndepMagTrivialSlice` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **J-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ 0

/-- **h-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **β-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh 0

end Ambient
end IsingModel
