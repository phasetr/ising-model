import IsingModel.ClusterExpansion.StrictPositivity.TanhBounds

/-!
# Cluster expansion strict positivity split — Mayer term filters and vanishing

Part of the split cluster-expansion strict-positivity layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-- **Filter-connected = filter-incompatible on `Fin 2`** (§18.4
sharpening): the cluster-sequence filter for n=2 (PR #1521) coincides
with the existing `PolymersIncompatible`-based filter (Step 597).
Direct corollary of `polymerSeqIncompatibilityGraph_two_connected_iff_incompatible`. -/
theorem mayerExpansionTerm_two_filter_connected_eq_incompat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (Fintype.piFinset (fun _ : Fin 2 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset (fun _ : Fin 2 => allPolymers G)).filter
        (fun ω => PolymersIncompatible (ω 0) (ω 1)) := by
  classical
  apply Finset.filter_congr
  intro ω _
  exact polymerSeqIncompatibilityGraph_two_connected_iff_incompatible ω

/-- **`mayerExpansionTerm = 0` for graphs with no polymers** (§18.4
sharpening): when `allPolymers G = ∅`, the n-th Mayer term vanishes
for every `n ≥ 1` and every `t`. Reason: `piFinset (fun _ : Fin n => ∅)`
is empty for `n ≥ 1`, so the sum is trivially zero. The `n = 0` case
is already covered by `mayerExpansionTerm_zero`. Companion to
`polymerFreeEnergy_eq_zero_of_no_polymers` (Step 621): both sides of
the Mayer identity vanish when no polymers exist. -/
theorem mayerExpansionTerm_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (n : ℕ) (t : ℝ) :
    mayerExpansionTerm G n t = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact mayerExpansionTerm_zero G t
  · unfold mayerExpansionTerm
    -- n ≥ 1: piFinset (fun _ : Fin n => ∅) = ∅
    have h_empty : Fintype.piFinset (fun _ : Fin n => allPolymers G) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      rw [Fintype.mem_piFinset, h_no] at hω
      simpa using hω ⟨0, hn⟩
    rw [h_empty, Finset.sum_empty]


end IsingModel
