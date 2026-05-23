import IsingModel.ClusterExpansion.Families.VertexDisjoint

/-!
# Cluster polymer families split — polymer partition function and bounds

Part of the split cluster-expansion families layer (Issue #1850).
-/

namespace IsingModel

open Finset

/-- **Polymer model partition function (abstract)**: given a reference
finite universe of polymer candidates `Ω : Finset (Finset (Sym2 ι))`
and a weight function `z : Finset (Sym2 ι) → ℝ`, the polymer model
partition function is
`Ξ(Ω, z) = ∑_{Γ ⊆ Ω, Γ compatible} ∏_{P ∈ Γ} z(P)`,
where compatibility is pairwise edge-disjointness.

`Classical.dec` is used to decide compatibility of arbitrary
sub-families because `IsPolymer` (involving edge-connectedness via
`Relation.ReflTransGen`) is not constructively decidable. -/
noncomputable def polymerPartition {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Ω : Finset (Finset (Sym2 ι))) (z : Finset (Sym2 ι) → ℝ) : ℝ := by
  classical
  exact ∑ Γ ∈ Ω.powerset.filter (fun Γ => IsCompatiblePolymerFamily G Γ),
    ∏ P ∈ Γ, z P

/-- **Polymer partition function on a single polymer**: when the
universe is `{P}` for a single polymer `P`, the partition function
equals `1 + z(P)` (the empty family contributes `1`, the singleton
family contributes `z(P)`). -/
theorem polymerPartition_singleton {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    (z : Finset (Sym2 ι) → ℝ) :
    polymerPartition G ({P} : Finset (Finset (Sym2 ι))) z = 1 + z P := by
  classical
  unfold polymerPartition
  -- powerset of `{P}` is `{∅, {P}}`; both are compatible.
  have hpow : ({P} : Finset (Finset (Sym2 ι))).powerset =
      ({∅, {P}} : Finset (Finset (Finset (Sym2 ι)))) := by
    ext Γ
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [hpow]
  rw [show ({∅, {P}} : Finset (Finset (Finset (Sym2 ι)))).filter
      (fun Γ => IsCompatiblePolymerFamily G Γ) = {∅, {P}} from ?_]
  · rw [Finset.sum_pair (a := (∅ : Finset (Finset (Sym2 ι))))
        (b := ({P} : Finset (Finset (Sym2 ι))))
        (by simp)]
    simp
  · ext Γ
    rw [Finset.mem_filter]
    refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
    rcases Finset.mem_insert.mp h with h | h
    · subst h; exact IsCompatiblePolymerFamily.empty G
    · rw [Finset.mem_singleton] at h
      subst h
      exact (isCompatiblePolymerFamily_singleton G P).mpr hP

/-- **Polymer partition function is at least 1 under non-negative
weights**: if `z(P) ≥ 0` for every `P ∈ Ω`, then
`polymerPartition G Ω z ≥ 1`. The empty sub-family always contributes
exactly 1 to the sum. -/
theorem polymerPartition_ge_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Ω : Finset (Finset (Sym2 ι))) {z : Finset (Sym2 ι) → ℝ}
    (hz : ∀ Q ∈ Ω, 0 ≤ z Q) :
    1 ≤ polymerPartition G Ω z := by
  classical
  unfold polymerPartition
  -- Split off the empty sub-family: contributes 1 to the sum.
  have h_empty_in : (∅ : Finset (Finset (Sym2 ι))) ∈
      Ω.powerset.filter (fun Γ => IsCompatiblePolymerFamily G Γ) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.empty_mem_powerset _,
      IsCompatiblePolymerFamily.empty G⟩
  have h_split := Finset.add_sum_erase _ (fun Γ => ∏ P ∈ Γ, z P) h_empty_in
  simp only [Finset.prod_empty] at h_split
  have h_other_nn : 0 ≤ ∑ Γ ∈ (Ω.powerset.filter
        (fun Γ => IsCompatiblePolymerFamily G Γ)).erase ∅,
        ∏ P ∈ Γ, z P := by
    apply Finset.sum_nonneg
    intro Γ hΓ
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hΓ
    obtain ⟨_, hsub, _⟩ := hΓ
    apply Finset.prod_nonneg
    intro P hPΓ
    exact hz P (hsub hPΓ)
  linarith

/-- **Polymer partition function on an empty universe equals 1**: the
only sub-family is `∅`, which is compatible with empty product `1`. -/
theorem polymerPartition_empty {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (z : Finset (Sym2 ι) → ℝ) :
    polymerPartition G (∅ : Finset (Finset (Sym2 ι))) z = 1 := by
  classical
  unfold polymerPartition
  rw [Finset.powerset_empty,
      Finset.filter_eq_self.mpr fun Γ hΓ => by
        rw [Finset.mem_singleton] at hΓ
        subst hΓ
        exact IsCompatiblePolymerFamily.empty G]
  simp


end IsingModel
