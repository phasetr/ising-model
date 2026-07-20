import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.ClusterExpansion.Families.VertexDisjoint
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FibreBijection
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FibreFilterSum

/-!
# The `r!`-to-one colour-class fibre (3/5): the per-`m` family-tuple identity

Structural split (3/5) of
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre`.
This child holds the per-`m` Mayer–Montroll identity
`vdFamilyTuple_sum_eq_seq_coloring_sum`, expressing the family-tuple weight sum as the
`1/r!`-normalised activity-weighted colouring count, together with the over-long-sequence
vanishing `properSurjectiveColorings_empty_of_card_lt`.  See the
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre` facade module for the
full contents overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Family-tuple sum as a polymer-sequence colouring sum** (per-`m` Mayer–Montroll identity):
the family-tuple weight sum equals the activity-weighted proper-surjective-colouring count over
polymer sequences of all lengths, normalised by `1/r!`.  Each family-tuple `Ω` is recovered `r!`
times (one per ordering of its labelled polymers), so the `1/r!` cancels and exactly `W(Ω)`
survives. -/
theorem vdFamilyTuple_sum_eq_seq_coloring_sum {m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) :
    (∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
        ∏ i : Fin m, ∏ P ∈ Ω i, t ^ P.card) =
      ∑ r ∈ Finset.range (m * (allPolymers G).card + 1),
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω := by
  classical
  have hr : ∀ r : ℕ,
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
        (if (labelledPolymers Ω).card = r then ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card else 0) := by
    intro r
    have key : ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          clusterSeqActivity t ω =
        ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdCompatiblePolymerFamilies G).erase ∅),
          (if (labelledPolymers Ω).card = r then
            (r.factorial : ℝ) * ∏ a : Fin m, ∏ P ∈ Ω a, t ^ P.card else 0) := by
      rw [seq_count_eq_fiberwise]
      refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
      rw [Fintype.mem_piFinset] at hΩ
      exact fiber_filter_sum_eval G t hΩ
    rw [show (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω) =
        (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
            clusterSeqActivity t ω) / (r.factorial : ℝ) from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun ω _ => by ring), key, Finset.sum_div]
    refine Finset.sum_congr rfl (fun Ω _ => ?_)
    split_ifs with h
    · rw [mul_div_cancel_left₀ _ (by positivity : (r.factorial : ℝ) ≠ 0)]
    · rw [zero_div]
  simp_rw [hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  have hsub : ∀ a, Ω a ⊆ allPolymers G :=
    fun a => (mem_vdCompatiblePolymerFamilies.mp (Finset.mem_erase.mp (hΩ a)).2).1
  have hlt : (labelledPolymers Ω).card < m * (allPolymers G).card + 1 := by
    rw [card_labelledPolymers]
    calc ∑ a : Fin m, (Ω a).card
        ≤ ∑ _a : Fin m, (allPolymers G).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card (hsub a))
      _ = m * (allPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ < m * (allPolymers G).card + 1 := Nat.lt_succ_self _
  rw [Finset.sum_eq_single_of_mem ((labelledPolymers Ω).card) (Finset.mem_range.mpr hlt)
      (fun r _ hr => if_neg (fun h => hr h.symm)), if_pos rfl]

/-- **No proper surjective colouring of an over-long sequence**: for `ω` valued in
`allPolymers G`, if the sequence length `r` exceeds `m·|allPolymers G|` then there is no
proper surjective `m`-colouring of its incompatibility graph (the `m` colour classes each lie
in `allPolymers`, of total size `r ≤ m·|allPolymers|`). -/
theorem properSurjectiveColorings_empty_of_card_lt {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {ω : Fin r → Finset (Sym2 ι)} (hω : ∀ i, ω i ∈ allPolymers G)
    (hr : m * (allPolymers G).card < r) :
    properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hproper, hsurj⟩ := (mem_properSurjectiveColorings _).mp hc
  have e : Fin r ≃ ↥(labelledPolymers (colorClass ω c)) :=
    Equiv.ofBijective (seqColoringForward (fun a => rfl))
      ⟨seqColoringForward_injective G hω hproper (fun a => rfl),
        seqColoringForward_surjective (fun a => rfl)⟩
  have hcard : r = ∑ a : Fin m, (colorClass ω c a).card := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe, card_labelledPolymers] at hc
    exact hc
  have hsub : ∀ a, colorClass ω c a ⊆ allPolymers G := by
    intro a P hP
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hP
    exact hω i
  have hle : (∑ a : Fin m, (colorClass ω c a).card) ≤ m * (allPolymers G).card := by
    calc ∑ a : Fin m, (colorClass ω c a).card
        ≤ ∑ _a : Fin m, (allPolymers G).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card (hsub a))
      _ = m * (allPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

end IsingModel
