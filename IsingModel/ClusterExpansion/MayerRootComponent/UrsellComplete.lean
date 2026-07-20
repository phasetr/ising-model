import IsingModel.ClusterExpansion.AlternatingCompleteGraph
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.MayerRootComponent.RecurrenceClosedForm

/-!
# Mayer K_n root-component recurrence (5/5): Ursell coefficients of a complete cluster

Structural split (5/5) of `IsingModel.ClusterExpansion.MayerRootComponent`.
This child holds the Ursell-coefficient consequences for a pairwise-incompatible polymer
sequence, whose incompatibility graph is complete: the normalised connected-spanning signed
sum form of `ursellCoefficient`, the completeness criterion, the transported closed form and
the resulting value `ϕ^T (ω) = (-1)^(n-1) / n`.  See the
`IsingModel.ClusterExpansion.MayerRootComponent` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

/-- **Ursell coefficient as a normalised connected-spanning signed sum**: by
definition `ϕ^T(ω) = c(G(ω)) / n!` where `G(ω) = polymerSeqIncompatibilityGraph ω`
and `c = alternatingConnectedSubgraphSum`. -/
theorem ursellCoefficient_eq_alternatingConnectedSubgraphSum_div
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    ursellCoefficient ω
      = alternatingConnectedSubgraphSum (polymerSeqIncompatibilityGraph ω)
          / (Nat.factorial n : ℝ) := by
  rfl

/-- **Complete incompatibility graph from pairwise incompatibility**: if every two
distinct polymers in the sequence are incompatible, the index-side incompatibility
graph is the complete graph `⊤`. -/
theorem polymerSeqIncompatibilityGraph_eq_top_of_pairwise
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    polymerSeqIncompatibilityGraph ω = ⊤ := by
  ext i j
  rw [polymerSeqIncompatibilityGraph_adj, SimpleGraph.top_adj]
  exact ⟨fun hij => hij.1, fun hne => ⟨hne, h i j hne⟩⟩

/-- **Connected-spanning signed sum of a complete incompatibility cluster**: when
all polymers are pairwise incompatible (so `G(ω) = ⊤`), the connected-spanning
signed sum equals the Mayer K_n value `(-1)^(n-1)(n-1)!`. Transfers the closed form
`alternatingConnectedSubgraphSum_completeGraph_closed_form` through the identity
isomorphism `G(ω) ≃g ⊤` (`alternatingConnectedSubgraphSum_iso`). -/
theorem alternatingConnectedSubgraphSum_polymerSeq_complete
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hn : 1 ≤ n) (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    alternatingConnectedSubgraphSum (polymerSeqIncompatibilityGraph ω)
      = (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) := by
  have hg := polymerSeqIncompatibilityGraph_eq_top_of_pairwise h
  have e : polymerSeqIncompatibilityGraph ω ≃g (⊤ : SimpleGraph (Fin n)) :=
    { toEquiv := Equiv.refl (Fin n)
      map_rel_iff' := fun {a b} => by simp only [Equiv.refl_apply]; rw [hg] }
  rw [alternatingConnectedSubgraphSum_iso e,
    alternatingConnectedSubgraphSum_completeGraph_closed_form hn]

/-- **Ursell coefficient of a fully-incompatible cluster**: when all `n` polymers
are pairwise incompatible, `ϕ^T(ω) = (-1)^(n-1)(n-1)!/n!`. -/
theorem ursellCoefficient_complete
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hn : 1 ≤ n) (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    ursellCoefficient ω
      = (-1 : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) / (Nat.factorial n : ℝ) := by
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div,
    alternatingConnectedSubgraphSum_polymerSeq_complete hn h]

/-- **Ursell coefficient of a fully-incompatible cluster (reduced form)**: the
classic single-cluster Mayer value `ϕ^T(ω) = (-1)^(n-1)/n` for `n` pairwise
incompatible polymers (cancelling `(n-1)!` against `n! = n·(n-1)!`). -/
theorem ursellCoefficient_complete_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hn : 1 ≤ n) (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    ursellCoefficient ω = (-1 : ℝ) ^ (n - 1) / (n : ℝ) := by
  rw [ursellCoefficient_complete hn h]
  have hfac : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    rw [← Nat.mul_factorial_pred (show n ≠ 0 by omega)]; push_cast; ring
  have hfacne : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (n - 1)).ne'
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [hfac]
  field_simp

end IsingModel
