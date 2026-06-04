import IsingModel.Concrete.CubicExhaustion
import IsingModel.Lattice

/-!
# Cubic-box adjacency geometry (screening foundation, Issue #3565)

Geometric facts about how nearest-neighbour adjacency in `latticeGraph d`
interacts with the nested cubic boxes `cubicBox d n`.  These are the foundation
for the **screening** lemma of the infinite-volume `+` state (Issue #3565): they
encode that, for the `+` boundary state on a box, the inner free region is
shielded from the outer shell, and that the outer shell together with its
neighbours stays inside the frozen region.

* `latticeGraph_adj_abs_le_one` — adjacent sites differ by at most `1` in each
  coordinate.
* `cubicBox_adj_mem_succ` — a neighbour of a `cubicBox d n` site lies in
  `cubicBox d (n+1)` (the inner region only reaches one box further out).
* `cubicBox_shell_adj_not_mem_inner` — for `n + 1 ≤ m`, a site of the shell
  `cubicBox d (m+1) ∖ cubicBox d m` and any of its neighbours lie outside
  `cubicBox d n` (so all shell-touching interactions are between frozen `+`
  spins).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Adjacent sites differ by at most one in each coordinate**: if
`(latticeGraph d).Adj x y` (i.e. `∑_i |x i − y i| = 1`), then `|x i − y i| ≤ 1`
for every coordinate `i` (each term is bounded by the total). -/
theorem latticeGraph_adj_abs_le_one {d : ℕ} {x y : Fin d → ℤ}
    (hadj : (latticeGraph d).Adj x y) (i : Fin d) : |x i - y i| ≤ 1 := by
  have hsum : (∑ j : Fin d, |x j - y j|) = 1 := hadj
  have hle : |x i - y i| ≤ ∑ j : Fin d, |x j - y j| :=
    Finset.single_le_sum (f := fun j => |x j - y j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  rw [hsum] at hle
  exact hle

/-- **A neighbour of a `cubicBox d n` site lies in `cubicBox d (n+1)`**: if
`x ∈ cubicBox d n` and `x` is adjacent to `y`, then `y ∈ cubicBox d (n+1)` (each
coordinate of `y` is within `1` of `x`'s, hence in `[-(n+1), n+1]`).  This says
the inner free region of a `+` box state reaches only one box further out. -/
theorem cubicBox_adj_mem_succ {d n : ℕ} {x y : Fin d → ℤ}
    (hx : x ∈ cubicBox d n) (hadj : (latticeGraph d).Adj x y) :
    y ∈ cubicBox d (n + 1) := by
  rw [mem_cubicBox]
  intro i
  have hxi := (mem_cubicBox.mp hx) i
  have habs := latticeGraph_adj_abs_le_one hadj i
  rw [abs_le] at habs
  push_cast
  omega

/-- **The shell and its neighbours avoid the inner box**: for `n + 1 ≤ m`, if
`x ∈ cubicBox d (m+1) ∖ cubicBox d m` (a shell site) and `x` is adjacent to `y`,
then `y ∉ cubicBox d n`.  Indeed `x` has a coordinate of absolute value `m + 1`
(it is in `box (m+1)` but not `box m`), and that coordinate of `y` is at least
`m ≥ n + 1 > n`.  Hence every interaction touching the shell is between sites
frozen to `+`. -/
theorem cubicBox_shell_adj_not_mem_inner {d n m : ℕ} (hnm : n + 1 ≤ m)
    {x y : Fin d → ℤ}
    (hx : x ∈ cubicBox d (m + 1) \ cubicBox d m)
    (hadj : (latticeGraph d).Adj x y) :
    y ∉ cubicBox d n := by
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxM, hxm⟩ := hx
  -- `x` has a coordinate `i` with `|x i| = m + 1`.
  rw [mem_cubicBox] at hxM
  have hxm' : ∃ i, ¬ (-(m : ℤ) ≤ x i ∧ x i ≤ m) := by
    by_contra hcon
    exact hxm (mem_cubicBox.mpr (fun i => not_not.mp (not_exists.mp hcon i)))
  obtain ⟨i, hi⟩ := hxm'
  have hMi := hxM i
  have habs := latticeGraph_adj_abs_le_one hadj i
  rw [abs_le] at habs
  intro hy
  have hyi := (mem_cubicBox.mp hy) i
  push_cast at hMi hi hyi habs
  omega

end Ambient

end IsingModel
