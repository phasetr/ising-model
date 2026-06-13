import IsingModel.ClusterExpansion.MayerCore.Terms

/-!
# Vanishing of mixed clusters for non-interacting polymers (GJ §18.4–§18.5)

For a non-interacting polymer gas (distinct polymers pairwise compatible, i.e.
vertex-disjoint), a polymer *sequence* `ω` with two distinct values has a
disconnected incompatibility graph (edges connect only equal values), so its
Ursell coefficient vanishes (`ursellCoefficient_eq_zero_of_pairwise_compatible_not_constant`).
Consequently the `n`-th Mayer term collapses to the diagonal (constant-sequence,
single-polymer) contributions
`mayerExpansionTerm G n t = ∑_{P} ϕ^T(P,…,P)·(t^|P|)^n`
(`mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible`).  Summed over the
multiplicity `n`, the single-polymer series `∑_m ϕ^T(P,…,P)·(t^|P|)^m =
log(1+t^|P|)` then recovers the independent free energy — the cluster-expansion
verification of the exactly-solvable case.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mixed-cluster Ursell vanishing**: if every two distinct values of the
sequence `ω` are compatible (`¬ PolymersIncompatible`) and `ω` is not constant,
then the incompatibility graph is disconnected (edges connect only equal values,
so the two indices with different values lie in different components) and the
Ursell coefficient vanishes. -/
theorem ursellCoefficient_eq_zero_of_pairwise_compatible_not_constant
    {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hcompat : ∀ i j, ω i ≠ ω j → ¬ PolymersIncompatible (ω i) (ω j))
    (hnc : ∃ i j, ω i ≠ ω j) :
    ursellCoefficient ω = 0 := by
  apply ursellCoefficient_eq_zero_of_disconnected
  intro hconn
  obtain ⟨u, v, huv⟩ := hnc
  -- reachability preserves the polymer value: adjacency forces equal values
  have hval : ∀ a b, (polymerSeqIncompatibilityGraph ω).Reachable a b → ω a = ω b := by
    intro a b h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | @tail x y _ hadj ih =>
      rw [polymerSeqIncompatibilityGraph_adj] at hadj
      rw [ih]
      by_contra hxy
      exact hcompat x y hxy hadj.2
  exact huv (hval u v (hconn.preconnected u v))

omit [Fintype ι] in
/-- The constant sequence is in the `n`-fold polymer power finset iff its value is
a polymer (for `n ≥ 1`). -/
theorem const_mem_piFinset_allPolymers
    {G : SimpleGraph ι} [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) {P : Finset (Sym2 ι)} :
    (fun _ : Fin n => P) ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G)
      ↔ P ∈ allPolymers G := by
  rw [Fintype.mem_piFinset]
  exact ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩

/-- **Mayer term collapses to the diagonal for non-interacting polymers** (GJ
§18.4–§18.5): if distinct polymers of `G` are pairwise compatible, then for
`n ≥ 1` the `n`-th Mayer term is the sum of the constant-sequence (single-polymer
multiplicity-`n`) contributions, `mayerExpansionTerm G n t =
∑_{P} ϕ^T(P,…,P)·(t^|P|)^n`.  Every non-constant sequence vanishes by
`ursellCoefficient_eq_zero_of_pairwise_compatible_not_constant`, and the constant
sequences reindex to `allPolymers G`. -/
theorem mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G, P ≠ Q → ¬ PolymersIncompatible P Q)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    mayerExpansionTerm G n t =
      ∑ P ∈ allPolymers G,
        ursellCoefficient (fun _ : Fin n => P) * (t ^ P.card) ^ n := by
  classical
  unfold mayerExpansionTerm
  -- restrict to constant sequences (non-constant ones vanish)
  have hstep : (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        ursellCoefficient ω * clusterSeqActivity t ω)
      = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∀ i j, ω i = ω j), ursellCoefficient ω * clusterSeqActivity t ω := by
    symm
    refine Finset.sum_filter_of_ne (fun ω hω hne => ?_)
    rw [Fintype.mem_piFinset] at hω
    by_contra hncon
    refine hne (mul_eq_zero.mpr (Or.inl ?_))
    refine ursellCoefficient_eq_zero_of_pairwise_compatible_not_constant
      (fun i j hij => hcompat (ω i) (hω i) (ω j) (hω j) hij) ?_
    by_contra h
    apply hncon
    intro i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  rw [hstep]
  -- reindex constant sequences to allPolymers
  refine Finset.sum_bij (fun (ω : Fin n → Finset (Sym2 ι)) (_ : ω ∈ _) => ω ⟨0, hn⟩) ?_ ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hω
    exact hω.1 _
  · intro ω₁ hω₁ ω₂ hω₂ heq
    rw [Finset.mem_filter] at hω₁ hω₂
    funext i
    rw [hω₁.2 i ⟨0, hn⟩, hω₂.2 i ⟨0, hn⟩]
    exact heq
  · intro P hP
    refine ⟨fun _ => P, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨(const_mem_piFinset_allPolymers hn).mpr hP, fun _ _ => rfl⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω
    have hc : ∀ i, ω i = ω ⟨0, hn⟩ := fun i => hω.2 i ⟨0, hn⟩
    have hu : ursellCoefficient ω = ursellCoefficient (fun _ : Fin n => ω ⟨0, hn⟩) := by
      congr 1; funext i; exact hc i
    have hz : clusterSeqActivity t ω = (t ^ (ω ⟨0, hn⟩).card) ^ n := by
      rw [clusterSeqActivity,
        show (∏ i, t ^ (ω i).card) = ∏ _i : Fin n, t ^ (ω ⟨0, hn⟩).card from
          Finset.prod_congr rfl (fun i _ => by rw [hc i]),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hu, hz]

end IsingModel
