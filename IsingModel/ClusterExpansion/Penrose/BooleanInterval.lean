import IsingModel.ClusterExpansion.MayerCore

/-!
# Boolean-interval signed-sum cancellation (Penrose tree-graph, GJ §18.4-18.5)

This is the first genuinely *unconditional* building block of the from-scratch
Penrose tree-graph inequality
`|alternatingConnectedSubgraphSum G| ≤ numSpanningTrees G`, the sole remaining
hard input for general interacting cluster-expansion convergence (Issue #3954).

Penrose's argument partitions the connected spanning edge-subsets of a graph into
Boolean intervals `[lo, hi] = {S | lo ⊆ S ⊆ hi}`, each indexed by a spanning tree
`lo` with addable part `hi \ lo`.  Over each such interval the alternating sign
sum `∑_{lo ⊆ S ⊆ hi} (-1)^{|S|}` collapses: it vanishes when `hi \ lo` is nonempty
and equals the survivor `(-1)^{|lo|}` when `hi = lo`.  This file proves exactly
that cancellation, generically over a `DecidableEq` type, in both `ℤ` and `ℝ`.

No hypothesis structures are introduced: every statement here is an
unconditionally-true fact about finite sets, consumed directly by the later
Penrose collapse.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.
- Penrose tree-graph inequality (Brydges' lectures).
- mathlib `Finset.sum_powerset_neg_one_pow_card`,
  `Finset.sum_powerset_neg_one_pow_card_of_nonempty`.
-/

namespace IsingModel.Penrose

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Boolean interval** `[lo, hi] = {S | lo ⊆ S ∧ S ⊆ hi}` as a `Finset` of
`Finset`s, realised as the elements of `hi.powerset` containing `lo`. -/
def booleanInterval (lo hi : Finset α) : Finset (Finset α) :=
  hi.powerset.filter (fun S => lo ⊆ S)

/-- **Membership in a Boolean interval**: `S ∈ booleanInterval lo hi` iff
`lo ⊆ S ⊆ hi`. -/
@[simp]
theorem mem_booleanInterval {lo hi S : Finset α} :
    S ∈ booleanInterval lo hi ↔ lo ⊆ S ∧ S ⊆ hi := by
  unfold booleanInterval
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **An ill-formed interval is empty**: if `lo` is not contained in `hi`, no set
`S` can satisfy `lo ⊆ S ⊆ hi`, so the interval is empty. -/
theorem booleanInterval_eq_empty_of_not_subset {lo hi : Finset α} (h : ¬ lo ⊆ hi) :
    booleanInterval lo hi = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro S hS
  rw [mem_booleanInterval] at hS
  exact h (hS.1.trans hS.2)

/-- **Disjointness of the lower endpoint from the addable part**: `lo` is disjoint
from any subset `U` of the addable edges `hi \ lo`. -/
theorem disjoint_lo_of_subset_sdiff {lo hi U : Finset α} (hU : U ⊆ hi \ lo) :
    Disjoint lo U := by
  rw [Finset.disjoint_left]
  intro a ha haU
  exact (Finset.mem_sdiff.mp (hU haU)).2 ha

/-- **Boolean interval parametrised by its addable part**: when `lo ⊆ hi`, the
interval `[lo, hi]` is the image of the powerset of the addable edges `hi \ lo`
under `U ↦ lo ∪ U`.  This is the standard parametrisation `S = lo ⊔ (S \ lo)`. -/
theorem booleanInterval_eq_image_powerset_sdiff {lo hi : Finset α} (h : lo ⊆ hi) :
    booleanInterval lo hi = (hi \ lo).powerset.image (fun U => lo ∪ U) := by
  ext S
  rw [mem_booleanInterval, Finset.mem_image]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨S \ lo, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hhi (le_refl lo)
    · rw [Finset.union_sdiff_of_subset hlo]
  · rintro ⟨U, hU, rfl⟩
    rw [Finset.mem_powerset] at hU
    exact ⟨Finset.subset_union_left,
      Finset.union_subset h (hU.trans Finset.sdiff_subset)⟩

/-- **Cardinality of an interval element**: for `U ⊆ hi \ lo`, the set `lo ∪ U`
has cardinality `|lo| + |U|` because `lo` and `U` are disjoint. -/
theorem card_union_of_subset_sdiff {lo hi U : Finset α} (hU : U ⊆ hi \ lo) :
    (lo ∪ U).card = lo.card + U.card :=
  Finset.card_union_of_disjoint (disjoint_lo_of_subset_sdiff hU)

/-- **Injectivity of the interval parametrisation**: for `U₁, U₂ ⊆ hi \ lo`,
`lo ∪ U₁ = lo ∪ U₂` forces `U₁ = U₂` (recovering `U = (lo ∪ U) \ lo`). -/
theorem union_lo_inj {lo hi U₁ U₂ : Finset α} (h₁ : U₁ ⊆ hi \ lo)
    (h₂ : U₂ ⊆ hi \ lo) (heq : lo ∪ U₁ = lo ∪ U₂) : U₁ = U₂ := by
  have hd₁ : Disjoint lo U₁ := disjoint_lo_of_subset_sdiff h₁
  have hd₂ : Disjoint lo U₂ := disjoint_lo_of_subset_sdiff h₂
  have hcg := congrArg (fun S => S \ lo) heq
  simpa only [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂]
    using hcg

/-- **Boolean-interval signed-sum factorisation (`ℤ`)**: for `lo ⊆ hi`,
`∑_{lo ⊆ S ⊆ hi} (-1)^{|S|} = (-1)^{|lo|} · ∑_{U ⊆ hi \ lo} (-1)^{|U|}`. -/
theorem sum_booleanInterval_neg_one_pow_card_int {lo hi : Finset α} (h : lo ⊆ hi) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℤ) ^ S.card)
      = (-1 : ℤ) ^ lo.card * ∑ U ∈ (hi \ lo).powerset, (-1 : ℤ) ^ U.card := by
  rw [booleanInterval_eq_image_powerset_sdiff h,
    Finset.sum_image (fun U₁ h₁ U₂ h₂ => union_lo_inj
      (Finset.mem_powerset.mp h₁) (Finset.mem_powerset.mp h₂)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  rw [Finset.mem_powerset] at hU
  rw [card_union_of_subset_sdiff hU, pow_add]

/-- **Boolean-interval cancellation (`ℤ`)**: when the addable part `hi \ lo` is
nonempty, the alternating sum over `[lo, hi]` vanishes. -/
theorem sum_booleanInterval_neg_one_pow_card_int_of_sdiff_nonempty
    {lo hi : Finset α} (h : lo ⊆ hi) (hne : (hi \ lo).Nonempty) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℤ) ^ S.card) = 0 := by
  rw [sum_booleanInterval_neg_one_pow_card_int h,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hne, mul_zero]

/-- **Boolean-interval survivor (`ℤ`)**: a singleton interval `hi = lo` contributes
exactly `(-1)^{|lo|}`. -/
theorem sum_booleanInterval_neg_one_pow_card_int_of_eq
    {lo hi : Finset α} (h : hi = lo) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℤ) ^ S.card) = (-1 : ℤ) ^ lo.card := by
  subst h
  rw [sum_booleanInterval_neg_one_pow_card_int (le_refl hi), Finset.sdiff_self,
    Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero, mul_one]

/-- **Cast bridge**: the real alternating sum over a Boolean interval equals the
integer-cast of the integer alternating sum. -/
theorem sum_booleanInterval_neg_one_pow_card_real_eq_cast (lo hi : Finset α) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℝ) ^ S.card)
      = (((∑ S ∈ booleanInterval lo hi, (-1 : ℤ) ^ S.card) : ℤ) : ℝ) := by
  push_cast
  rfl

/-- **Boolean-interval signed-sum factorisation (`ℝ`)**: the real form of
`sum_booleanInterval_neg_one_pow_card_int`. -/
theorem sum_booleanInterval_neg_one_pow_card_real {lo hi : Finset α} (h : lo ⊆ hi) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℝ) ^ S.card)
      = (-1 : ℝ) ^ lo.card * ∑ U ∈ (hi \ lo).powerset, (-1 : ℝ) ^ U.card := by
  rw [sum_booleanInterval_neg_one_pow_card_real_eq_cast,
    sum_booleanInterval_neg_one_pow_card_int h]
  push_cast
  rfl

/-- **Boolean-interval cancellation (`ℝ`)**: when the addable part `hi \ lo` is
nonempty, the real alternating sum over `[lo, hi]` vanishes.  This is the
sign-cancellation that drives the Penrose collapse. -/
theorem sum_booleanInterval_neg_one_pow_card_real_of_sdiff_nonempty
    {lo hi : Finset α} (h : lo ⊆ hi) (hne : (hi \ lo).Nonempty) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℝ) ^ S.card) = 0 := by
  rw [sum_booleanInterval_neg_one_pow_card_real_eq_cast,
    sum_booleanInterval_neg_one_pow_card_int_of_sdiff_nonempty h hne, Int.cast_zero]

/-- **Boolean-interval survivor (`ℝ`)**: a singleton interval `hi = lo` contributes
exactly `(-1)^{|lo|}`.  These are the only intervals surviving the collapse. -/
theorem sum_booleanInterval_neg_one_pow_card_real_of_eq
    {lo hi : Finset α} (h : hi = lo) :
    (∑ S ∈ booleanInterval lo hi, (-1 : ℝ) ^ S.card) = (-1 : ℝ) ^ lo.card := by
  rw [sum_booleanInterval_neg_one_pow_card_real_eq_cast,
    sum_booleanInterval_neg_one_pow_card_int_of_eq h]
  push_cast
  rfl

end IsingModel.Penrose
