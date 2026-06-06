import IsingModel.Peierls.SingleOrbitReach
import IsingModel.Peierls.SingleOrbitContact
import IsingModel.Peierls.DualCutConnected

/-!
# The orbit's left sites lie in one `F`-component (FV §3.7.2)

Iterating the per-step `F`-reachability of `SingleOrbitReach`: the left site of any forward iterate
of `d` is reachable within `F` from `d.left` (`reachableWithin_left_iterate`), hence any dart `e` in
`d`'s orbit has `e.left` reachable within `F` from `d.left` (`reachableWithin_left_of_sameOrbit`),
and symmetrically (`reachableWithin_left_of_sameOrbit_symm`). Contrapositively, two darts whose left
sites lie in different `F`-components are in different orbits
(`not_sameOrbit_of_not_reachableWithin_left`). This is the `F`-side necessary condition for the
single-orbit property: it confines each orbit to one `F`-component of left sites. (It does not by
itself force a single orbit when `F` is connected — that needs the complementary planar input via
contact-pair chains.)

* `reachableWithin_left_iterate` — the iterate's left site is `F`-reachable.
* `reachableWithin_left_of_sameOrbit` / `_symm` — orbit left sites are `F`-reachable.
* `not_sameOrbit_of_not_reachableWithin_left` — the `F`-side orbit separation.
* `reachableWithin_left_of_mem_dartOrbit` — every dart in the orbit finset.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **The left site of a forward iterate is `F`-reachable** from `d.left` (iterating the per-step
bridge through transitivity). -/
theorem reachableWithin_left_iterate (d : BoundaryDart F) (n : ℕ) :
    ReachableWithin (latticeGraph 2) F d.left (BoundaryDart.nextDart^[n] d).left := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (reachableWithin_left_nextDart (BoundaryDart.nextDart^[m] d))

/-- **Orbit left sites are `F`-reachable**: if `d.SameOrbit e` then `e.left` is reachable within `F`
from `d.left`. -/
theorem reachableWithin_left_of_sameOrbit (d e : BoundaryDart F) (h : d.SameOrbit e) :
    ReachableWithin (latticeGraph 2) F d.left e.left := by
  obtain ⟨n, hn⟩ := h
  rw [← hn]
  exact reachableWithin_left_iterate d n

/-- **Symmetric form**: if `d.SameOrbit e` then `d.left` is reachable within `F` from `e.left`. -/
theorem reachableWithin_left_of_sameOrbit_symm (d e : BoundaryDart F) (h : d.SameOrbit e) :
    ReachableWithin (latticeGraph 2) F e.left d.left :=
  reachableWithin_left_of_sameOrbit e d h.symm

/-- **The `F`-side orbit separation**: if `e.left` is not reachable within `F` from `d.left`, then
`d` and `e` are in different orbits. -/
theorem not_sameOrbit_of_not_reachableWithin_left (d e : BoundaryDart F)
    (h : ¬ ReachableWithin (latticeGraph 2) F d.left e.left) : ¬ d.SameOrbit e :=
  fun hso => h (reachableWithin_left_of_sameOrbit d e hso)

/-- **The orbit finset's left sites are `F`-reachable**: every `e` in `dartOrbit d` has `e.left`
reachable within `F` from `d.left`. -/
theorem reachableWithin_left_of_mem_dartOrbit (d e : BoundaryDart F) (h : e ∈ dartOrbit d) :
    ReachableWithin (latticeGraph 2) F d.left e.left :=
  reachableWithin_left_of_sameOrbit d e (mem_dartOrbit.mp h)

end IsingModel
