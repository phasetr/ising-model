import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Counting by anchor cover (FV §3.7.2)

The Peierls contour count partitions the droplet family by which fixed ray anchor pins each contour.
The general counting principle: if every element of a finite family `D` carries *some* anchor in a
finite set `Z`, and each anchor class has at most `M` members, then `|D| ≤ |Z| · M`. With the
`r` ray anchors `z_0, …, z_{r-1}` (first-exit bound `k < r`) and the per-anchor count `M = 16^r`,
this yields the volume-independent contour bound `r · 16^r ≤ 32^r`.

* `card_le_of_anchor_cover` — the anchor-cover counting bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Counting by anchor cover**: if every element of `D` satisfies `P a z` for some anchor `z ∈ Z`,
and each anchor class `{a ∈ D | P a z}` has at most `M` elements, then `|D| ≤ |Z| · M`. -/
theorem card_le_of_anchor_cover {α β : Type*} (D : Finset α) (Z : Finset β)
    (P : α → β → Prop) [∀ a z, Decidable (P a z)] (M : ℕ)
    (hcover : ∀ a ∈ D, ∃ z ∈ Z, P a z)
    (hbound : ∀ z ∈ Z, (D.filter (fun a => P a z)).card ≤ M) :
    D.card ≤ Z.card * M := by
  classical
  calc D.card
      ≤ (Z.biUnion (fun z => D.filter (fun a => P a z))).card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨z, hz, hP⟩ := hcover a ha
        exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨ha, hP⟩⟩
    _ ≤ ∑ z ∈ Z, (D.filter (fun a => P a z)).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Z, M := Finset.sum_le_sum (fun z hz => hbound z hz)
    _ = Z.card * M := by simp [Finset.sum_const, mul_comm]

end IsingModel
