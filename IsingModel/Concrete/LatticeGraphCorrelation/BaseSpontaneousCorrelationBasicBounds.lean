import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d spontaneousCorrelation basic bound wrappers

Narrow child module for three ℤ^d basic
`spontaneousCorrelation_latticeGraph_*` bound wrappers extracted from
`BaseSpontaneousCorrelation.lean`:

* `neg_one_le_spontaneousCorrelation_latticeGraph`,
* `spontaneousCorrelation_latticeGraph_nonneg`,
* `spontaneousCorrelation_latticeGraph_le_one`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `-1 ≤ spontaneousCorrelation`** (ferromagnetic). -/
theorem neg_one_le_spontaneousCorrelation_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    -1 ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  neg_one_le_spontaneousCorrelation (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d spontaneousCorrelation ≥ 0** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    0 ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  spontaneousCorrelation_nonneg (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d spontaneousCorrelation ≤ 1** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A ≤ 1 :=
  spontaneousCorrelation_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

end Ambient
end IsingModel
