import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationΛ + magnetizationAlongEx monotone wrappers

Narrow child module for six ℤ^d
`magnetization*_latticeGraph_monotone_{h,beta,J}` wrappers. Each
wrapper is a thin pass-through to the corresponding ambient
`magnetization*_monotone_*` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d magnetizationΛ h-monotonicity**: `MonotoneOn` in `h` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun h : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationΛ β-monotonicity**: `MonotoneOn` in `β` on `Ioi 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : ↑Λ) :
    MonotoneOn
      (fun β : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi 0) :=
  magnetizationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-- **ℤ^d magnetizationΛ J-monotonicity**: `MonotoneOn` in `J` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun J : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-! ## Moved: magnetizationAlongEx monotone wrappers

The three wrappers
`magnetizationAlongExhaustion_latticeGraph_monotone_h`,
`magnetizationAlongExhaustion_latticeGraph_monotone_beta`,
`magnetizationAlongExhaustion_latticeGraph_monotone_J` now live in
`UniformMagMagnetizationTrivialMonotoneAlongEx.lean`. -/



end Ambient
end IsingModel
