/- BaseSpontaneousCorrelation.lean
Narrow child module for the 9 ℤ^d `spontaneousCorrelation_latticeGraph_*`
plus `spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph`
wrappers extracted from `Base.lean` in PR #2032. Each is a thin
pass-through to the abstract `spontaneousCorrelation_*` /
`spontaneousMagnetization_monotone_ambient_subgraph` lemma at
`latticeGraph d`. The theorem names are unchanged from the former
`Base` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

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

/-- **ℤ^d J-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d) Λ hβ A

/-- **ℤ^d β-direction monotonicity of `spontaneousCorrelation`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d) Λ hJ A

/-- **ℤ^d `spontaneousCorrelation ... {i} = spontaneousMagnetization ... i`**
(any-Exhaustion): singleton-set spontaneous correlation equals
spontaneous magnetization. -/
theorem spontaneousCorrelation_latticeGraph_singleton_eq_spontaneousMagnetization
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (i : Fin d → ℤ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β {i}
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (IsingModel.latticeGraph d) Λ J β i

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
