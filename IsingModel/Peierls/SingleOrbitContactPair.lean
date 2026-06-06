import IsingModel.Peierls.SingleOrbitContact

/-!
# Contact pairs as a type (FV §3.7.2)

A **contact pair** of a region `F` is an ordered adjacent pair `(inSite, outSite)` with
`inSite ∈ F` and `outSite ∉ F`. `SingleOrbitContact` showed these correspond to boundary darts; here
the correspondence is packaged as a type `ContactPair F` with maps in both directions
(`BoundaryDart.toContactPair`, `ContactPair.toDart`) forming a round trip
(`toContactPair_toDart`, `toDart_toContactPair`). Working with contact pairs — rather than right
sites — is the route (per a focused codex design pass) to the complement side of the single-orbit
property: the elementary "contact steps" that vary only the in- or out-site avoid the left-turn gap
that breaks the naive orbit-step complement invariant.

* `ContactPair` — the type of contact pairs of `F`.
* `ContactPair.toDart` / `toDart_left` / `toDart_right` — the realizing dart and its sites.
* `BoundaryDart.toContactPair` — the contact pair of a dart.
* `toContactPair_toDart` / `toDart_toContactPair` — the round trip.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A contact pair of `F`**: an ordered adjacent pair, first site in `F`, second outside. -/
structure ContactPair (F : Finset (Fin 2 → ℤ)) where
  /-- The `F`-side site. -/
  inSite : Fin 2 → ℤ
  /-- The complement-side site. -/
  outSite : Fin 2 → ℤ
  /-- The in-site lies in `F`. -/
  inSite_mem : inSite ∈ F
  /-- The out-site lies outside `F`. -/
  outSite_not_mem : outSite ∉ F
  /-- The two sites are lattice-adjacent. -/
  adj : (latticeGraph 2).Adj inSite outSite

/-- **The boundary dart realising a contact pair** (left site `inSite`, right site `outSite`). -/
noncomputable def ContactPair.toDart (c : ContactPair F) : BoundaryDart F :=
  (exists_boundaryDart_of_contact c.inSite_mem c.outSite_not_mem c.adj).choose

/-- **The realizing dart has left site `inSite`**. -/
theorem ContactPair.toDart_left (c : ContactPair F) : c.toDart.left = c.inSite :=
  (exists_boundaryDart_of_contact c.inSite_mem c.outSite_not_mem c.adj).choose_spec.1

/-- **The realizing dart has right site `outSite`**. -/
theorem ContactPair.toDart_right (c : ContactPair F) : c.toDart.right = c.outSite :=
  (exists_boundaryDart_of_contact c.inSite_mem c.outSite_not_mem c.adj).choose_spec.2

/-- **The contact pair of a boundary dart** (in-site `left`, out-site `right`). -/
def BoundaryDart.toContactPair (d : BoundaryDart F) : ContactPair F where
  inSite := d.left
  outSite := d.right
  inSite_mem := d.left_mem
  outSite_not_mem := d.right_not_mem
  adj := d.adj_left_right

/-- **Round trip dart → contact pair → dart**: a dart is recovered from its contact pair (a dart is
determined by its sites). -/
theorem toContactPair_toDart (d : BoundaryDart F) : d.toContactPair.toDart = d := by
  apply BoundaryDart.ext_of_left_right
  · rw [ContactPair.toDart_left]; rfl
  · rw [ContactPair.toDart_right]; rfl

/-- **Round trip contact pair → dart → contact pair**: a contact pair is recovered from its dart. -/
theorem toDart_toContactPair (c : ContactPair F) : c.toDart.toContactPair = c := by
  cases c with
  | mk inSite outSite hin hout hadj =>
    have hL : (ContactPair.mk inSite outSite hin hout hadj).toDart.left = inSite :=
      ContactPair.toDart_left _
    have hR : (ContactPair.mk inSite outSite hin hout hadj).toDart.right = outSite :=
      ContactPair.toDart_right _
    simp only [BoundaryDart.toContactPair, hL, hR]

end IsingModel
