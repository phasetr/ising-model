import IsingModel.Peierls.SingleOrbitAdvanceMem
import IsingModel.Peierls.SingleOrbitContactGen
import IsingModel.Peierls.SingleOrbitWedge

/-!
# Orbit successor dichotomy at a first hit (FV §3.7.2)

At the first rotation hitting `F` (`harc`/`hstop`), the next `nextDart` step is a contact move
(`reflTransGen_contactMove_iterate`), and its left site is determined by one membership test on the
straight out-site `r = rightSite (nextDart^[n] d).head (turnLeft^[n] d.dir)`:

* if `r ∉ F` the orbit **slides straight** to the chosen `F`-neighbour
  `d.left + (turnLeft^[n] d.dir).vec`;
* if `r ∈ F` the orbit **turns right** (a concave corner), its successor left site being `r`.

(`firstHit_nextDart_inSite_dichotomy`.) This makes the orbit's actual successor explicit. It does
**not** discharge the `hsame`/single-orbit crux: by `reflTransGen_contactMove_iff_sameOrbit`,
contact-move connectivity equals same-orbit, so "the orbit visits every boundary contact pair of a
filled connected component" — the conclusion this dynamics must reach — *is* the discrete-Jordan
single-curve property itself, which the contact-pair bookkeeping relocates but does not remove.

* `firstHit_nextDart_inSite_dichotomy` — the straight/right-turn dichotomy of the orbit successor.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **Orbit successor dichotomy at a first hit**: after the left fan stops at the first rotation
landing in `F`, the next step is a contact move, and either the straight out-site is outside `F`
(the orbit slides to the `F`-neighbour) or inside `F` (the orbit turns right, with successor left
site that out-site). -/
theorem firstHit_nextDart_inSite_dichotomy (d : BoundaryDart F) {n : ℕ}
    (harc : ∀ i < n, d.left + ((Dir2.turnLeft^[i]) d.dir).vec ∉ F)
    (hstop : d.left + ((Dir2.turnLeft^[n]) d.dir).vec ∈ F) :
    Relation.ReflTransGen ContactMove d.toContactPair
        (BoundaryDart.nextDart^[n + 1] d).toContactPair ∧
      ((rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir) ∉ F ∧
          (BoundaryDart.nextDart^[n + 1] d).left
            = d.left + ((Dir2.turnLeft^[n]) d.dir).vec) ∨
        (rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir) ∈ F ∧
          (BoundaryDart.nextDart^[n + 1] d).left
            = rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir))) := by
  refine ⟨reflTransGen_contactMove_iterate d (n + 1), ?_⟩
  by_cases hr : rightSite (BoundaryDart.nextDart^[n] d).head ((Dir2.turnLeft^[n]) d.dir) ∈ F
  · right
    refine ⟨hr, ?_⟩
    have hfan : d.LeftFanPrefix n := leftFanPrefix_of_outSites_not_mem d harc
    have hLinv : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head
        (BoundaryDart.nextDart^[n] d).dir.turnLeft := by
      rw [leftFan_next_turnLeft_valid_iff d hfan]; exact not_not.mpr hstop
    have hSinv : ¬ ValidAt F (BoundaryDart.nextDart^[n] d).head
        (BoundaryDart.nextDart^[n] d).dir := by
      intro hval
      have hh := hval.2
      rw [dir_eq_iterate_of_leftFanPrefix d hfan] at hh
      exact hh hr
    rw [Function.iterate_succ_apply', left_nextDart_of_turnRight _ hLinv hSinv,
      dir_eq_iterate_of_leftFanPrefix d hfan]
  · left
    exact ⟨hr, (sameOrbit_advance_of_membership d harc hstop hr).2⟩

end IsingModel
