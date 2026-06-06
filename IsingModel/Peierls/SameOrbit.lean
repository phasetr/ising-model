import IsingModel.Peierls.DartOrbit

/-!
# The same-orbit equivalence on boundary darts (FV §3.7.2)

Two boundary darts are in the **same orbit** when one is reached from the other by iterating
`nextDart`. Since `nextDart` is a bijection of the finite dart type (every dart is periodic), this
is an equivalence relation. The discrete Jordan single-curve theorem
(`boundaryDart_single_orbit_of_connected_filled`) will say that for a connected, filled region all
darts are in one orbit; this file provides the equivalence-relation scaffolding.

* `BoundaryDart.left`, `BoundaryDart.right` — the left/right sites of a dart.
* `BoundaryDart.SameOrbit` — reachability under iterated `nextDart`.
* `SameOrbit.refl`, `SameOrbit.symm`, `SameOrbit.trans` — it is an equivalence relation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- The **left site** of a boundary dart (the `F`-side of the cut edge it crosses). -/
def BoundaryDart.left (d : BoundaryDart F) : Fin 2 → ℤ := leftSite d.tail d.dir

/-- The **right site** of a boundary dart (the complement side of the cut edge). -/
def BoundaryDart.right (d : BoundaryDart F) : Fin 2 → ℤ := rightSite d.tail d.dir

/-- **Same orbit**: `e` is reached from `d` by iterating `nextDart`. -/
def BoundaryDart.SameOrbit (d e : BoundaryDart F) : Prop :=
  ∃ n : ℕ, (BoundaryDart.nextDart^[n]) d = e

/-- The same-orbit relation is reflexive. -/
@[refl] theorem BoundaryDart.SameOrbit.refl (d : BoundaryDart F) : d.SameOrbit d :=
  ⟨0, rfl⟩

/-- The same-orbit relation is transitive. -/
theorem BoundaryDart.SameOrbit.trans {d e f : BoundaryDart F} (h₁ : d.SameOrbit e)
    (h₂ : e.SameOrbit f) : d.SameOrbit f := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨m + n, by rw [Function.iterate_add_apply, hn]; exact hm⟩

/-- The same-orbit relation is symmetric (using that every dart is periodic under `nextDart`). -/
theorem BoundaryDart.SameOrbit.symm {d e : BoundaryDart F} (h : d.SameOrbit e) : e.SameOrbit d := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨p, hp, hpd⟩ := nextDart_periodic d
  refine ⟨p * (n + 1) - n, ?_⟩
  have hge : n ≤ p * (n + 1) := by nlinarith [hp]
  rw [← hn, ← Function.iterate_add_apply, Nat.sub_add_cancel hge, Function.iterate_mul]
  exact Function.iterate_fixed hpd (n + 1)

end IsingModel
