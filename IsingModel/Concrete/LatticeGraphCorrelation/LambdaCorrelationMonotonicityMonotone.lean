import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-Λ `correlationΛ` monotone wrappers

Narrow child module for three ℤ^d Λ-induced
`correlationΛ_latticeGraph_monotone_{h,beta,J}` wrappers extracted from
`LambdaCorrelationMonotonicity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d per-Λ h-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d per-Λ β-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {h : ℝ} (hh : 0 ≤ h) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A

/-- **ℤ^d per-Λ J-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {h : ℝ} (hh : 0 ≤ h)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun J : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

end Ambient
end IsingModel
