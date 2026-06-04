import IsingModel.Lattice
import IsingModel.Concrete.CubicExhaustion
import IsingModel.AmbientLattice.Defs.Core

/-!
# Connectivity of the cubic box induced graph

The induced subgraph of the cubic lattice `latticeGraph d` on a centred box
`cubicBox d n = [-n, n]^d` is **connected**: any two sites of the box are joined by
a lattice path that stays inside the box (move one coordinate at a time towards the
target; intermediate coordinates lie between the endpoints, hence in `[-n, n]`).

This is a reusable abstraction for infinite-volume work along the cubic
exhaustion: it discharges the reachability / positive-distance hypotheses
(`0 < dist`) of the finite-volume correlation-decay bounds at every exhaustion
stage.

* `cubicBox_exists_adj_step` — a single distance-reducing lattice step that stays
  in the box (box-aware companion of `latticeDistance_exists_adj_step`);
* `inducedGraph_cubicBox_reachable` — any two box sites are reachable;
* `inducedGraph_cubicBox_dist_pos` — distinct box sites are at positive distance.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Box-aware distance-reducing step**: for `x, j` in the cubic box at ℓ¹
distance `m + 1`, there is a neighbour `x'` of `x` (in `latticeGraph d`) that is
itself in the box and one step closer to `j`.  The step moves the single
differing coordinate of `x` one unit towards `j`, so the new coordinate stays
between the endpoints and hence in `[-n, n]`. -/
theorem cubicBox_exists_adj_step (d n : ℕ) {x j : Fin d → ℤ}
    (hx : x ∈ cubicBox d n) (hj : j ∈ cubicBox d n) {m : ℕ}
    (hd : IsingModel.latticeDistance d x j = m + 1) :
    ∃ x', x' ∈ cubicBox d n ∧ (IsingModel.latticeGraph d).Adj x x'
      ∧ IsingModel.latticeDistance d x' j = m := by
  have hne : x ≠ j := fun he => by rw [he, IsingModel.latticeDistance_self] at hd; omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hxi := (mem_cubicBox.mp hx) i
  have hji := (mem_cubicBox.mp hj) i
  set v : ℤ := x i + (if x i < j i then 1 else -1) with hvdef
  have hvbox : -(n : ℤ) ≤ v ∧ v ≤ n := by
    rcases lt_trichotomy (x i) (j i) with hlt | heq | hgt
    · rw [hvdef, if_pos hlt]; omega
    · exact absurd heq hi
    · rw [hvdef, if_neg (not_lt.mpr hgt.le)]; omega
  refine ⟨Function.update x i v, ?_, ?_, ?_⟩
  · rw [mem_cubicBox]
    intro k
    by_cases hk : k = i
    · subst hk; rw [Function.update_self]; exact hvbox
    · rw [Function.update_of_ne hk]; exact (mem_cubicBox.mp hx) k
  · rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
    unfold IsingModel.latticeDistance
    rw [Finset.sum_eq_single i]
    · rw [Function.update_self]; omega
    · intro k _ hk; rw [Function.update_of_ne hk]; simp
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  · have hL : IsingModel.latticeDistance d (Function.update x i v) j
        = (v - j i).natAbs + ∑ k ∈ Finset.univ.erase i, (x k - j k).natAbs := by
      unfold IsingModel.latticeDistance
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    have hR : IsingModel.latticeDistance d x j
        = (x i - j i).natAbs + ∑ k ∈ Finset.univ.erase i, (x k - j k).natAbs := by
      unfold IsingModel.latticeDistance
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hstep : (v - j i).natAbs + 1 = (x i - j i).natAbs := by
      rcases lt_trichotomy (x i) (j i) with hlt | heq | hgt
      · rw [hvdef, if_pos hlt]; omega
      · exact absurd heq hi
      · rw [hvdef, if_neg (not_lt.mpr hgt.le)]; omega
    rw [hL]; rw [hR] at hd; omega

/-- **Induced-graph adjacency from lattice adjacency on the box**: lattice
adjacency of two box sites is exactly adjacency in the induced subgraph. -/
theorem inducedGraph_cubicBox_adj (d n : ℕ) {x x' : Fin d → ℤ}
    (hx : x ∈ cubicBox d n) (hx' : x' ∈ cubicBox d n)
    (h : (IsingModel.latticeGraph d).Adj x x') :
    (inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)).Adj ⟨x, hx⟩ ⟨x', hx'⟩ := h

/-- **The cubic box induced graph is connected**: any two sites of the box are
reachable in the induced subgraph (joined by a lattice path inside the box).
Proof by induction on the ℓ¹ distance to the target, stepping with
`cubicBox_exists_adj_step`. -/
theorem inducedGraph_cubicBox_reachable (d n : ℕ) (a b : ↑(cubicBox d n)) :
    (inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)).Reachable a b := by
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  suffices H : ∀ m (x : Fin d → ℤ) (hx : x ∈ cubicBox d n),
      IsingModel.latticeDistance d x y = m →
      (inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ by
    exact H _ x hx rfl
  intro m
  induction m with
  | zero =>
    intro x hx hd
    have hxy : x = y := (IsingModel.latticeDistance_eq_zero_iff d x y).mp hd
    subst hxy
    exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    intro x hx hd
    obtain ⟨x', hx', hadj, hd'⟩ := cubicBox_exists_adj_step d n hx hy hd
    exact (inducedGraph_cubicBox_adj d n hx hx' hadj).reachable.trans (ih x' hx' hd')

/-- **Distinct box sites are at positive distance** in the cubic box induced
graph (the box is connected, so distinct vertices are reachable).  This discharges
the reachability hypothesis of the finite-volume correlation-decay bounds. -/
theorem inducedGraph_cubicBox_dist_pos (d n : ℕ) {a b : ↑(cubicBox d n)} (hab : a ≠ b) :
    0 < (inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)).dist a b :=
  (inducedGraph_cubicBox_reachable d n a b).pos_dist_of_ne hab

end Ambient

end IsingModel
