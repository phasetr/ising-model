import IsingModel.Peierls.CubicBoxPreconnected
import IsingModel.Peierls.DualSupport

/-!
# Outer boundary shell and dual-support containment for the canonical cubic box (FV §3.7.2)

Continuing the canonical-box supply for `peierls_plusGibbsLiminf_pos_filled`, this file provides the
remaining geometric inputs for `cubicBox 2 n = [-n, n]²`:

* the dual support of a droplet stays in the one-larger box (`hdual` supply);
* the outer boundary shell `cubicOuterBoundaryTwo n`, with droplets disjoint from it confined to the
  interior, hence neighbour-closed (`hne` supply).

The shell's connectedness (`hBconn`) and corner basepoint (`hgB`), with the final assembly, are
deferred to the next PR.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph Ambient GridEdge2

/-- **A boundary dart's tail and head stay within the one-larger box**: if the region `F` is
contained in `[-m, m]²`, then since the dart's left site lies in `F` and its tail/head are within
unit `L∞` distance of that left site, both lie in `[-(m+1), m+1]²`. -/
theorem dart_tail_head_mem_cubicBox_succ {m : ℕ} {F : Finset (Fin 2 → ℤ)}
    (hF : F ⊆ cubicBox 2 m) (d : BoundaryDart F) :
    d.tail ∈ cubicBox 2 (m + 1) ∧ d.head ∈ cubicBox 2 (m + 1) := by
  obtain ⟨t, dir, hleft, hright⟩ := d
  have hmem := (mem_cubicBox).mp (hF hleft)
  have hm0 := hmem 0
  have hm1 := hmem 1
  refine ⟨?_, ?_⟩ <;> rw [mem_cubicBox] <;> intro i <;> fin_cases dir <;> fin_cases i <;>
    · norm_num [BoundaryDart.head, leftSite, Dir2.vec, unitVec2, Pi.add_apply, Pi.neg_apply,
        Pi.single_apply] at hm0 hm1 ⊢
      omega

/-- **The dual support of an interior droplet stays in the one-larger box**: if every vertex of `S`
lies in `[-m, m]²`, the dual support of `S.image val` lies in `[-(m+1), m+1]²`. This is the `hdual`
supply for the Peierls bound. -/
theorem dualSupport_subset_cubicBox_succ {n m : ℕ} {S : Finset ↑(cubicBox 2 n)}
    (hS : ∀ a ∈ S, a.val ∈ cubicBox 2 m) :
    dualSupport (S.image Subtype.val) ⊆ cubicBox 2 (m + 1) := by
  have hF : S.image Subtype.val ⊆ cubicBox 2 m := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hS a ha
  intro x hx
  rw [dualSupport, Finset.mem_union] at hx
  rcases hx with hx | hx
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact (dart_tail_head_mem_cubicBox_succ hF d).1
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact (dart_tail_head_mem_cubicBox_succ hF d).2

/-- **The outer boundary shell** of the cubic box `[-n, n]²`: the box vertices with some coordinate
equal to `±n`. Droplets disjoint from it are confined to the interior `[-(n-1), n-1]²`. -/
noncomputable def cubicOuterBoundaryTwo (n : ℕ) : Finset ↑(cubicBox 2 n) :=
  Finset.univ.filter
    (fun a => a.val 0 = (n : ℤ) ∨ a.val 0 = -(n : ℤ) ∨ a.val 1 = (n : ℤ) ∨ a.val 1 = -(n : ℤ))

/-- **Membership in the boundary shell**: a box vertex is in the shell iff some coordinate is
`±n`. -/
theorem mem_cubicOuterBoundaryTwo {n : ℕ} {a : ↑(cubicBox 2 n)} :
    a ∈ cubicOuterBoundaryTwo n ↔
      a.val 0 = (n : ℤ) ∨ a.val 0 = -(n : ℤ) ∨ a.val 1 = (n : ℤ) ∨ a.val 1 = -(n : ℤ) := by
  unfold cubicOuterBoundaryTwo
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ a)

/-- **A droplet disjoint from the boundary shell is interior**: every vertex of a droplet `S` of
`[-(n+1), n+1]²` disjoint from the shell lies in the strictly smaller box `[-n, n]²`. -/
theorem image_subset_cubicBox_of_disjoint_outerBoundary {n : ℕ}
    {S : Finset ↑(cubicBox 2 (n + 1))}
    (hdisj : Disjoint S (cubicOuterBoundaryTwo (n + 1))) :
    ∀ a ∈ S, a.val ∈ cubicBox 2 n := by
  intro a ha
  have hnotB := Finset.disjoint_left.mp hdisj ha
  rw [mem_cubicOuterBoundaryTwo] at hnotB
  simp only [not_or] at hnotB
  obtain ⟨h0, h0', h1, h1'⟩ := hnotB
  have hbox := (mem_cubicBox).mp a.property
  have hb0 := hbox 0
  have hb1 := hbox 1
  rw [mem_cubicBox]
  intro i
  fin_cases i <;> push_cast at h0 h0' h1 h1' hb0 hb1 ⊢ <;> omega

/-- **A droplet disjoint from the boundary shell is neighbour-closed**: combining
`image_subset_cubicBox_of_disjoint_outerBoundary` with `neighbourClosed_of_image_subset_inner`,
any droplet of `[-(n+1), n+1]²` disjoint from the outer shell is neighbour-closed. This is the `hne`
supply of the Peierls bound for the canonical exhaustion. -/
theorem neighbourClosed_of_disjoint_outerBoundary {n : ℕ}
    {S : Finset ↑(cubicBox 2 (n + 1))}
    (hdisj : Disjoint S (cubicOuterBoundaryTwo (n + 1))) :
    NeighbourClosed (cubicBox 2 (n + 1)) S :=
  neighbourClosed_of_image_subset_inner (le_refl (n + 1))
    (image_subset_cubicBox_of_disjoint_outerBoundary hdisj)

end IsingModel
