import IsingModel.RandomCurrent.Switching.SourceFilters

/-!
# Switching between two prescribed source sets

Comparisons between the source-conditioned sub-current Finsets at two prescribed source sets
`A` and `B`, for a current `n` on `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces,
under the hypothesis `symmDiff (n.sources G Λ) A = B`. The graph `G : SimpleGraph V` and the
finite volume `Λ : Finset V` are arbitrary.

Under that hypothesis `Current.subFinset_with_source G Λ n A` and
`Current.subFinset_with_source G Λ n B` have the same cardinality, and the sums over them of
`Current.weight G Λ β J m` times `Current.weight G Λ β J (n - m)` are equal. In the second
statement `β` and `J` are implicit binders standing after the symmetric-difference
hypothesis, and they are otherwise unconstrained: it holds for arbitrary real `β` and `J`.

Each statement here takes `[DecidableEq V]`, `[Fintype (inducedGraph G Λ).edgeSet]` and
`[DecidableEq ↥Λ]`, and the symmetric-difference equation is its only hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Switching Lemma — cardinality**: when `symmDiff (sources n) A = B`,
the bijection `m ↦ n - m` (involution by `sub_sub_self_of_le`) maps
`subFinset_with_source n A` bijectively to `subFinset_with_source n B`,
hence the two source-conditioned sub-current sets have equal cardinality.
This is the fixed-total source-swap step of the switching lemma, at witness
`k = n`: FV Lemma 3.56, p. 145 / Aizenman 1982 Lemma 3.1, p. 7. -/
theorem Current.subFinset_with_source_card_switching
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) :
    (Current.subFinset_with_source G Λ n A).card =
      (Current.subFinset_with_source G Λ n B).card := by
  have hBA : symmDiff (n.sources G Λ) B = A := by
    rw [← hAB]; exact symmDiff_symmDiff_cancel_left _ _
  refine Finset.card_nbij' (fun m => n - m) (fun m => n - m) ?_ ?_ ?_ ?_
  · -- forward: m ∈ subFinset_with_source n A → n-m ∈ subFinset_with_source n B
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 B).mpr (by rw [hm.2]; exact hAB)⟩
  · -- backward: m ∈ subFinset_with_source n B → n-m ∈ subFinset_with_source n A
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 A).mpr (by rw [hm.2]; exact hBA)⟩
  · -- left_inv: n-(n-m) = m for m ∈ subFinset_with_source n A
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm
    exact Current.sub_sub_self_of_le G Λ hm.1
  · -- right_inv: n-(n-m) = m for m ∈ subFinset_with_source n B
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm
    exact Current.sub_sub_self_of_le G Λ hm.1

set_option linter.unusedDecidableInType false in
/-- **Switching Lemma — weighted sum**: when `symmDiff (sources n) A = B`,
the bijection `m ↦ n - m` preserves the function `m ↦ w(m) * w(n - m)`
(since `w(n-m) * w(n-(n-m)) = w(n-m) * w(m)` by `sub_sub_self_of_le` + `mul_comm`),
so the weighted sums over `subFinset_with_source n A` and `subFinset_with_source n B` are equal.
Since `w(m) * w(n - m) = w(n) * ∏_e (n e).choose (m e)`, this is the binomial
identity FV (3.81) at witness `k = n`: FV Lemma 3.56, p. 145 /
Aizenman 1982 Lemma 3.1, p. 7. -/
theorem Current.sum_subFinset_with_source_weight_mul_weight_switching
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) {β J : ℝ} :
    ∑ m ∈ Current.subFinset_with_source G Λ n A,
        m.weight G Λ β J * (n - m).weight G Λ β J =
      ∑ m ∈ Current.subFinset_with_source G Λ n B,
        m.weight G Λ β J * (n - m).weight G Λ β J := by
  have hBA : symmDiff (n.sources G Λ) B = A := by
    rw [← hAB]; exact symmDiff_symmDiff_cancel_left _ _
  refine Finset.sum_nbij' (fun m => n - m) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
  · -- forward
    intro m hm
    rw [Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 B).mpr (by rw [hm.2]; exact hAB)⟩
  · -- backward
    intro m hm
    rw [Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 A).mpr (by rw [hm.2]; exact hBA)⟩
  · -- left_inv
    intro m hm
    exact Current.sub_sub_self_of_le G Λ
      ((Current.mem_subFinset_with_source_iff G Λ n A m).mp hm).1
  · -- right_inv
    intro m hm
    exact Current.sub_sub_self_of_le G Λ
      ((Current.mem_subFinset_with_source_iff G Λ n B m).mp hm).1
  · -- value: w(m)*w(n-m) = w(n-m)*w(n-(n-m)) = w(n-m)*w(m)
    intro m hm
    rw [Current.sub_sub_self_of_le G Λ
        ((Current.mem_subFinset_with_source_iff G Λ n A m).mp hm).1, mul_comm]

end Ambient
end IsingModel
