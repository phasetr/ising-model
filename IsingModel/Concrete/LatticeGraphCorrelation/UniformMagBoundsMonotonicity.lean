import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `magnetizationInfinite` bounds and exhaustion-independence wrappers

Records the uniform bounds on the ℤ^d infinite-volume magnetization and the independence of
the spontaneous magnetization from the chosen exhaustion — the facts that make the
infinite-volume magnetization a well-defined bounded observable.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d spontaneousMagnetization exhaustion-independence**:
any two exhaustions yield the same `spontaneousMagnetization`. -/
theorem spontaneousMagnetization_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β i :=
  spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ i

/-- **ℤ^d magnetizationInfinite ≤ 1** site-wise (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite ≥ 0** site-wise (any Exhaustion, ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** site-wise (any Exhaustion, ferromagnetic):
combines `magnetizationInfinite_latticeGraph_nonneg` (so `0 ≤ M`, hence
`-1 ≤ M`) with `magnetizationInfinite_latticeGraph_le_one`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 := by
  have hl := magnetizationInfinite_latticeGraph_nonneg d Λ p hf i
  have hu := magnetizationInfinite_latticeGraph_le_one d Λ p i
  exact abs_le.mpr ⟨by linarith, hu⟩

end Ambient

end IsingModel
