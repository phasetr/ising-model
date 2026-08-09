import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag

/-!
# Parameter monotonicity of the ℤ^d uniform magnetization

Concrete `IsingModel.latticeGraph d` statements along `Ambient.cubicExhaustion d`: the
uniform magnetization is monotone in each field of the parameter record separately, with
the others held fixed. It is monotone in the coupling on `Set.Ici 0` assuming a
non-negative external field and a positive inverse temperature, in the external field on
`Set.Ici 0` assuming a non-negative coupling and a positive inverse temperature, and in the
inverse temperature on `Set.Ioi 0` assuming a non-negative coupling and a non-negative
external field. No instance argument is taken.
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
