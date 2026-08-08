import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d parameter monotonicity of `correlationInfinite`

Records that the ℤ^d infinite-volume correlation is `MonotoneOn` in the coupling and in the
external field over `Set.Ici 0`, and in the inverse temperature over `Set.Ioi 0`, each
statement holding the two other parameters fixed under the sign conditions `0 ≤ J`, `0 ≤ h`,
`0 < β` as applicable. The exhaustion and the subset `A` are arbitrary.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationInfinite J-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

/-- **ℤ^d correlationInfinite h-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d correlationInfinite β-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A


end Ambient
end IsingModel
