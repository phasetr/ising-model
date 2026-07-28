/- BaseSpontaneousCorrelation.lean
Narrow child module for the two ℤ^d spontaneous-correlation bound
wrappers `abs_spontaneousCorrelation_latticeGraph_le_one` and
`spontaneousCorrelation_latticeGraph_sq_le_one`, plus the
`spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph`
companion, extracted from `Base.lean` in PR #2032. Each is a thin
pass-through to the abstract `abs_spontaneousCorrelation_le_one` /
`spontaneousCorrelation_sq_le_one` /
`spontaneousMagnetization_monotone_ambient_subgraph` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`Base` declarations.
-/
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

open scoped symmDiff

namespace IsingModel
namespace Ambient

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
