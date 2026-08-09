import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d spontaneous correlation and its comparison at positive external field

Concrete `latticeGraph d` statements about the spontaneous correlation of a fixed finite
subset of `Fin d → ℤ` and about the spontaneous magnetization at a fixed site.

At `Ambient.cubicExhaustion d`, and under `0 ≤ J` and `0 < β`, the spontaneous correlation
lies between `0` and `1`. Once the external field is taken strictly positive, the spontaneous
correlation is at most the infinite-volume correlation at that field — stated at
`Ambient.cubicExhaustion d` and along an arbitrary `Ambient.Exhaustion` alike — and, along an
arbitrary exhaustion, the spontaneous magnetization is at most the infinite-volume
magnetization at that field. No instance argument is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    0 ≤ spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **Upper bound on `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A ≤ 1 :=
  spontaneousCorrelation_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **ℤ^d `spontaneousMagnetization ≤ magnetizationInfinite`** at positive `h`. -/
theorem spontaneousMagnetization_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ hJ hβ hh i

/-- **Infimum bound** `spontaneousCorrelation ≤ correlationInfinite ⟨J, h, β⟩`
for `h > 0` on ℤ^d. -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ hh A

/-- **ℤ^d `spontaneousCorrelation ≤ correlationInfinite`** for `h > 0`
(any Exhaustion). -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    Λ hJ hβ hh A

end Ambient
end IsingModel
