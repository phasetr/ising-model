import IsingModel.Peierls.DropletInjective

/-!
# The mod-2 side-parity separation engine (FV §3.7.2)

The Friedli–Velenik §3.7.2 Peierls argument reduces, after the dual-cut bookkeeping of
`PlanarBondReduction.lean`, to the discrete-Jordan fact that two boundary darts whose inside
endpoints are connected inside `F` and whose outside endpoints are connected in the complement
of `F` lie in the same dual-cut component. The combinatorial heart of that fact is a **mod-2
side-parity** argument, isolated here in graph-agnostic form.

Fix a finite graph `G` and two vertex sets `A`, `F` with `cutEdges G A ⊆ cutEdges G F`. The
membership predicate `(· ∈ A)` is then a mod-2 potential that is preserved along any walk that
stays inside `F` and along any walk that stays outside `F`: an edge with both endpoints inside
`F` (or both outside `F`) cannot be a cut edge of `F`, hence cannot be a cut edge of `A`, so it
does not flip `A`-membership. A "crossing pair" `(dl, dr)` with `dl ∈ F`, `dr ∉ F` flips the
`A`-potential exactly when its primal edge is a cut edge of `A`; two crossing pairs joined by an
inside walk on the left and an outside walk on the right can therefore not be separated by such
an `A`.

* `mem_iff_of_reachable_edges_preserve` — a predicate-restricted reachability preserves
  `A`-membership when every in-predicate edge keeps `A`-membership.
* `mem_iff_of_cutEdges_subset_inside` / `_outside` — a `cutEdges`-subset edge inside (resp.
  outside) `F` keeps `A`-membership.
* `mem_iff_of_reachableWithin_cutEdges_subset` — inside-walk preservation of the `A`-potential.
* `mem_iff_of_reachableOutside_cutEdges_subset` — outside-walk preservation.
* `not_separated_of_inside_outside_reachable` — the separation contradiction: a crossing pair
  and a non-crossing pair cannot be inside/outside-connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*}

/-- **Predicate-restricted reachability preserves the `A`-potential**: if every `G`-edge whose
both endpoints satisfy `P` keeps `A`-membership, then any chain of such edges from `x` to `y`
has `x ∈ A ↔ y ∈ A`. The abstract mod-2 potential transport. -/
theorem mem_iff_of_reachable_edges_preserve {A : Finset ι} {P : ι → Prop} {G : SimpleGraph ι}
    (hpres : ∀ a b, G.Adj a b → P a → P b → (a ∈ A ↔ b ∈ A))
    {x y : ι} (h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ P a ∧ P b) x y) :
    (x ∈ A ↔ y ∈ A) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (hpres _ _ hbc.1 hbc.2.1 hbc.2.2)

variable [DecidableEq ι]

/-- **A `cutEdges`-subset edge inside `F` keeps `A`-membership**: if `cutEdges G A ⊆ cutEdges G F`
and `a, b ∈ F` are adjacent, then `a ∈ A ↔ b ∈ A` (else the edge would be a cut edge of `A`,
hence of `F`, impossible with both endpoints inside `F`). -/
theorem mem_iff_of_cutEdges_subset_inside {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {A F : Finset ι} (hsub : cutEdges G A ⊆ cutEdges G F)
    {a b : ι} (hadj : G.Adj a b) (ha : a ∈ F) (hb : b ∈ F) : (a ∈ A ↔ b ∈ A) := by
  by_contra hne
  have hcrossA : s(a, b) ∈ cutEdges G A := by
    rw [mem_cutEdges_iff]; exact ⟨hadj, by tauto⟩
  have hcrossF := hsub hcrossA
  rw [mem_cutEdges_iff] at hcrossF
  tauto

/-- **A `cutEdges`-subset edge outside `F` keeps `A`-membership**: the complement counterpart of
`mem_iff_of_cutEdges_subset_inside`, for adjacent `a, b ∉ F`. -/
theorem mem_iff_of_cutEdges_subset_outside {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {A F : Finset ι} (hsub : cutEdges G A ⊆ cutEdges G F)
    {a b : ι} (hadj : G.Adj a b) (ha : a ∉ F) (hb : b ∉ F) : (a ∈ A ↔ b ∈ A) := by
  by_contra hne
  have hcrossA : s(a, b) ∈ cutEdges G A := by
    rw [mem_cutEdges_iff]; exact ⟨hadj, by tauto⟩
  have hcrossF := hsub hcrossA
  rw [mem_cutEdges_iff] at hcrossF
  tauto

/-- **Inside-walk preservation of the `A`-potential**: under `cutEdges G A ⊆ cutEdges G F`, a walk
staying inside `F` (a `ReachableWithin G F` chain) preserves `A`-membership. -/
theorem mem_iff_of_reachableWithin_cutEdges_subset {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {A F : Finset ι} (hsub : cutEdges G A ⊆ cutEdges G F)
    {x y : ι} (h : ReachableWithin G F x y) : (x ∈ A ↔ y ∈ A) :=
  mem_iff_of_reachable_edges_preserve
    (fun _ _ hadj ha hb => mem_iff_of_cutEdges_subset_inside hsub hadj ha hb) h

/-- **Outside-walk preservation of the `A`-potential**: under `cutEdges G A ⊆ cutEdges G F`, a walk
staying outside `F` (a chain of complement-adjacencies) preserves `A`-membership. -/
theorem mem_iff_of_reachableOutside_cutEdges_subset {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {A F : Finset ι} (hsub : cutEdges G A ⊆ cutEdges G F)
    {x y : ι}
    (h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ F ∧ b ∉ F) x y) : (x ∈ A ↔ y ∈ A) :=
  mem_iff_of_reachable_edges_preserve
    (fun _ _ hadj ha hb => mem_iff_of_cutEdges_subset_outside hsub hadj ha hb) h

/-- **The separation contradiction**: under `cutEdges G A ⊆ cutEdges G F`, a crossing pair
`(dl, dr)` (its primal edge is a cut edge of `A`) and a non-crossing adjacent pair `(el, er)`
(its primal edge is not a cut edge of `A`) cannot have `dl` reach `el` inside `F` while `dr`
reaches `er` outside `F`. The mod-2 potential transports `dl ∈ A ↔ el ∈ A ↔ er ∈ A ↔ dr ∈ A`,
contradicting the flip `dl ∈ A ↔ ¬ dr ∈ A` of the crossing pair. -/
theorem not_separated_of_inside_outside_reachable {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {A F : Finset ι} (hsub : cutEdges G A ⊆ cutEdges G F)
    {dl dr el er : ι} (hd_cross : s(dl, dr) ∈ cutEdges G A)
    (he_ncross : s(el, er) ∉ cutEdges G A) (he_adj : G.Adj el er)
    (hin : ReachableWithin G F dl el)
    (hout : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ F ∧ b ∉ F) dr er) : False := by
  rw [mem_cutEdges_iff] at hd_cross he_ncross
  have hin' := mem_iff_of_reachableWithin_cutEdges_subset hsub hin
  have hout' := mem_iff_of_reachableOutside_cutEdges_subset hsub hout
  have hde : (dl ∈ A ↔ dr ∈ A) := hin'.trans ((by tauto : el ∈ A ↔ er ∈ A).trans hout'.symm)
  tauto

end IsingModel
