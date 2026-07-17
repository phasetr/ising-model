/- BaseSpontaneousCorrelation.lean
Narrow child module for the 9 ℤ^d `spontaneousCorrelation_latticeGraph_*`
plus `spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph`
wrappers extracted from `Base.lean` in PR #2032. Each is a thin
pass-through to the abstract `spontaneousCorrelation_*` /
`spontaneousMagnetization_monotone_ambient_subgraph` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`Base` declarations.
-/
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: spontaneousCorrelation basic bound wrappers

The three wrappers
`neg_one_le_spontaneousCorrelation_latticeGraph`,
`spontaneousCorrelation_latticeGraph_nonneg`,
`spontaneousCorrelation_latticeGraph_le_one` now live in
`BaseSpontaneousCorrelationBasicBounds.lean`. -/


/-! ## Moved: spontaneousCorrelation monotonicity + singleton wrappers

The three wrappers
`spontaneousCorrelation_latticeGraph_monotone_J`,
`spontaneousCorrelation_latticeGraph_monotone_beta`,
`spontaneousCorrelation_latticeGraph_singleton_eq_spontaneousMagnetization`
now live in `BaseSpontaneousCorrelationMonotone.lean`. -/


/-- **ℤ^d `|spontaneousCorrelation| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousCorrelation_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    |spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A| ≤ 1 :=
  abs_spontaneousCorrelation_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousCorrelation² ≤ 1`** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A ^ 2 ≤ 1 :=
  spontaneousCorrelation_sq_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousMagnetization_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization G₁ Λ J β i
      ≤ spontaneousMagnetization G₂ Λ J β i :=
  spontaneousMagnetization_monotone_ambient_subgraph hG Λ hJ hβ i

end Ambient

end IsingModel
