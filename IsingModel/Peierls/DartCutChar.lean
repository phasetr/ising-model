import IsingModel.Peierls.DartPrimalCut
import IsingModel.Peierls.DartOfCut

/-!
# Membership characterization of the primal cut (FV §3.7.2)

Combining the two halves of the dart–cut correspondence, an edge lies in `dartPrimalCut F` exactly
when it joins an `F`-vertex to a non-`F`-vertex: `dartPrimalCut F` *is* the lattice cut of `F`. The
`⊆` direction reads off each dart's `left_mem`/`right_not_mem` (its endpoints are adjacent,
`leftSite_adj_rightSite`); the `⊇` direction is `exists_dart_of_cut`.

* `leftSite_adj_rightSite` — a dart's two sites are lattice-adjacent.
* `mem_dartPrimalCut_iff` — `e ∈ dartPrimalCut F ↔` `e` is a cut edge of `F`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {F : Finset (Fin 2 → ℤ)}

/-- **A dart's two sites are lattice-adjacent**: `leftSite` and `rightSite` differ by the unit
vector `(turnLeft dir).vec`. -/
theorem leftSite_adj_rightSite (tail : Fin 2 → ℤ) (dir : Dir2) :
    (latticeGraph 2).Adj (leftSite tail dir) (rightSite tail dir) := by
  change (∑ i : Fin 2, |leftSite tail dir i - rightSite tail dir i|) = 1
  rw [Fin.sum_univ_two, rightSite]
  fin_cases dir <;>
    simp [leftSite, Dir2.turnLeft, Dir2.vec, unitVec2, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]

/-- **The primal cut is the lattice cut**: an edge lies in `dartPrimalCut F` iff it joins an
`F`-vertex to a non-`F`-vertex. -/
theorem mem_dartPrimalCut_iff {e : Sym2 (Fin 2 → ℤ)} :
    e ∈ dartPrimalCut F ↔
      ∃ a b, e = s(a, b) ∧ (latticeGraph 2).Adj a b ∧ a ∈ F ∧ b ∉ F := by
  classical
  constructor
  · intro he
    rw [dartPrimalCut, Finset.mem_image] at he
    obtain ⟨d, _, rfl⟩ := he
    exact ⟨leftSite d.tail d.dir, rightSite d.tail d.dir, rfl,
      leftSite_adj_rightSite d.tail d.dir, d.left_mem, d.right_not_mem⟩
  · rintro ⟨a, b, rfl, hadj, ha, hb⟩
    obtain ⟨d, hd⟩ := exists_dart_of_cut hadj ha hb
    rw [dartPrimalCut, Finset.mem_image]
    exact ⟨d, Finset.mem_univ d, hd⟩

end IsingModel
