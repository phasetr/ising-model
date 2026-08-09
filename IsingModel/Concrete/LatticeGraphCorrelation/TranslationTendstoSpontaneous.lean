import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d spontaneous quantities as the right-hand limit at zero external field

Concrete `latticeGraph d` statements that, under `0 ≤ J` and `0 < β`, the infinite-volume
correlation of a fixed finite subset of `Fin d → ℤ` converges to the spontaneous correlation
as the external field decreases to `0` from above, and that the infinite-volume magnetization
at a fixed site converges likewise to the spontaneous magnetization. The correlation form is
stated at `Ambient.cubicExhaustion d` and along an arbitrary `Ambient.Exhaustion`; the
magnetization form is stated along an arbitrary exhaustion. No instance argument is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ A

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **Right-limit** `magnetizationInfinite ⟨J, h, β⟩ → spontaneousMagnetization J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ i

end Ambient
end IsingModel
