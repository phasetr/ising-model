/- TwoPointMagnetizationMonotone.lean
Narrow child module for the 5 ℤ^d magnetization monotonicity wrappers
(`spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_{J,beta}`,
`magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_{J,h,beta}`)
extracted from `TwoPoint.lean` in PR #2026. The theorem names are
unchanged from the former `TwoPoint` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **J-monotonicity of `spontaneousMagnetization` on ℤ^d** at any site. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ i

/-- **β-monotonicity of `spontaneousMagnetization` on ℤ^d** at any site. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ i

/-- **J-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ i

/-- **h-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ i

/-- **β-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh i

end Ambient

end IsingModel
