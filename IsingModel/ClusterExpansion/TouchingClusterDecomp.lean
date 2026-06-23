import IsingModel.ClusterExpansion.AvoidingRatioExp

/-!
# Touching-cluster decomposition for the avoiding delete-edges graph

This file rewrites the difference between the `n`-th complex Mayer term of `G` and the
corresponding term of `Gavoid G C` as a finite sum over cluster sequences containing at least one
polymer that touches `polymerSupport C`, and records the immediate per-`n` norm bound.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polymers of the avoiding graph form a sub-finset of the polymers of the original graph. -/
theorem allPolymers_Gavoid_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) :
    allPolymers (Gavoid G C) ⊆ allPolymers G := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  intro P hP
  rw [allPolymers_Gavoid G C] at hP
  exact (Finset.mem_filter.mp hP).1

/-- The product finset of avoiding-polymer sequences embeds in the product finset of all
polymer sequences. -/
theorem piFinset_allPolymers_Gavoid_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) :
    Fintype.piFinset (fun _ : Fin n => allPolymers (Gavoid G C)) ⊆
      Fintype.piFinset (fun _ : Fin n => allPolymers G) := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  exact Fintype.piFinset_subset _ _ (fun _ => allPolymers_Gavoid_subset G C)

/-- The finite difference of `n`-th Mayer terms is the sum over the product-finset complement.
Current Mathlib exposes `Finset.sum_sdiff`; on versions with `Finset.sum_sdiff_eq_sub`, the
last two proof lines can be replaced by that subtraction-oriented lemma. -/
theorem mayerExpansionTermComplex_sub_Gavoid_eq_sdiff_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (z : ℂ) :
    mayerExpansionTermComplex G n z - mayerExpansionTermComplex (Gavoid G C) n z =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allPolymers (Gavoid G C))),
        (ursellCoefficient ω : ℂ) * clusterSeqActivityComplex z ω := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  let sG : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allPolymers G)
  let sA : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allPolymers (Gavoid G C))
  let f : (Fin n → Finset (Sym2 ι)) → ℂ :=
    fun ω => (ursellCoefficient ω : ℂ) * clusterSeqActivityComplex z ω
  have hsub : sA ⊆ sG := by
    dsimp [sA, sG]
    exact piFinset_allPolymers_Gavoid_subset G C n
  have hsum := Finset.sum_sdiff (s₁ := sA) (s₂ := sG) (f := f) hsub
  unfold mayerExpansionTermComplex
  change (∑ ω ∈ sG, f ω) - (∑ ω ∈ sA, f ω) = ∑ ω ∈ sG \ sA, f ω
  rw [← hsum]
  ring

/-- Membership in the product-finset complement is equivalent to a sequence of polymers of `G`
with at least one polymer touching `polymerSupport C`. -/
theorem mem_piFinset_sdiff_iff_exists_touching
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {n : ℕ} {ω : Fin n → Finset (Sym2 ι)} :
    ω ∈
        (Fintype.piFinset (fun _ : Fin n => allPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allPolymers (Gavoid G C))) ↔
      (∀ i, ω i ∈ allPolymers G) ∧
        ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i) := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  constructor
  · intro h
    rw [Finset.mem_sdiff] at h
    have hG : ∀ i, ω i ∈ allPolymers G := Fintype.mem_piFinset.mp h.1
    have hnotA : ¬ ∀ i, ω i ∈ allPolymers (Gavoid G C) := by
      intro hA
      exact h.2 (Fintype.mem_piFinset.mpr hA)
    obtain ⟨i, hi⟩ := not_forall.mp hnotA
    refine ⟨hG, i, ?_⟩
    intro hdisj
    apply hi
    rw [allPolymers_Gavoid G C, Finset.mem_filter]
    refine ⟨hG i, ?_⟩
    exact (subset_edgeFinset_Gavoid_iff G C (ω i)).mpr
      ⟨(mem_allPolymers.mp (hG i)).isEven.subset, hdisj⟩
  · rintro ⟨hG, ⟨i, htouch⟩⟩
    rw [Finset.mem_sdiff]
    refine ⟨Fintype.mem_piFinset.mpr hG, ?_⟩
    intro hA
    have hiA : ω i ∈ allPolymers (Gavoid G C) := Fintype.mem_piFinset.mp hA i
    rw [allPolymers_Gavoid G C, Finset.mem_filter] at hiA
    have hsubAvoid : ω i ⊆ (Gavoid G C).edgeFinset := hiA.2
    have hdisj : IsPolymerVertexDisjoint C (ω i) :=
      ((subset_edgeFinset_Gavoid_iff G C (ω i)).mp hsubAvoid).2
    exact htouch hdisj

open Classical in
/-- The finite difference of `n`-th Mayer terms is the sum over cluster sequences containing at
least one polymer touching `polymerSupport C`. -/
theorem mayerExpansionTermComplex_sub_Gavoid_eq_touching_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (z : ℂ) :
    mayerExpansionTermComplex G n z - mayerExpansionTermComplex (Gavoid G C) n z =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        (ursellCoefficient ω : ℂ) * clusterSeqActivityComplex z ω := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  rw [mayerExpansionTermComplex_sub_Gavoid_eq_sdiff_sum
    (G := G) (C := C) (n := n) (z := z)]
  apply Finset.sum_congr
  · ext ω
    rw [Finset.mem_filter]
    constructor
    · intro h
      have ht :=
        (mem_piFinset_sdiff_iff_exists_touching
          (G := G) (C := C) (n := n) (ω := ω)).mp h
      exact ⟨(Finset.mem_sdiff.mp h).1, ht.2⟩
    · rintro ⟨hG, htouch⟩
      exact
        (mem_piFinset_sdiff_iff_exists_touching
          (G := G) (C := C) (n := n) (ω := ω)).mpr
          ⟨Fintype.mem_piFinset.mp hG, htouch⟩
  · intro ω _hω
    rfl

open Classical in
/-- The norm of the finite difference of `n`-th Mayer terms is bounded by the sum of the norms of
the touching-cluster summands. -/
theorem norm_mayerExpansionTermComplex_sub_Gavoid_le
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (z : ℂ) :
    ‖mayerExpansionTermComplex G n z - mayerExpansionTermComplex (Gavoid G C) n z‖
      ≤ ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        ‖(ursellCoefficient ω : ℂ)‖ * ∏ i, ‖z‖ ^ (ω i).card := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  rw [mayerExpansionTermComplex_sub_Gavoid_eq_touching_sum
    (G := G) (C := C) (n := n) (z := z)]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun ω _hω => le_of_eq ?_
  rw [norm_mul, clusterSeqActivityComplex_norm]

end IsingModel
