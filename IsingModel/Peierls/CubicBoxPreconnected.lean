import IsingModel.Concrete.CubicExhaustion
import IsingModel.Peierls.GridEdge2
import IsingModel.Peierls.PlanarBondSeparationBridge
import IsingModel.Peierls.ContourInjective
import IsingModel.Peierls.DartOfCut

/-!
# Preconnectedness of the induced 2D cubic box graph (FV §3.7.2)

The Peierls magnetization bound `peierls_plusGibbsLiminf_pos_filled` takes a per-stage
preconnectedness hypothesis `hpre n` on the induced box graph. For the canonical cubic exhaustion
`cubicBox 2 n = [-n, n]²` this holds outright: any box vertex is connected to the origin by walking
each coordinate down to `0` one unit step at a time, every intermediate point staying in the box.

* `zero_mem_cubicBox_two` — the origin lies in every cubic box.
* `inducedCubicBox_two_reachable_zero` — every box vertex reaches the origin.
* `inducedCubicBox_two_preconnected` — the induced 2D cubic box graph is preconnected.
* `neighbourClosed_of_image_subset_inner` — an interior droplet (image in a strictly smaller box) is
  neighbour-closed in the cubic box, the `hne` supply for the Peierls bound.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph Ambient GridEdge2

/-- **The origin lies in every cubic box** `[-n, n]²`. -/
theorem zero_mem_cubicBox_two (n : ℕ) : (0 : Fin 2 → ℤ) ∈ cubicBox 2 n := by
  rw [mem_cubicBox]
  intro i
  simp only [Pi.zero_apply]
  omega

/-- **A unit coordinate shift of a box point**: `x + e_j` written coordinatewise. -/
theorem add_unitVec2_apply (x : Fin 2 → ℤ) (j i : Fin 2) :
    (x + unitVec2 j) i = x i + (if i = j then 1 else 0) := by
  simp [unitVec2, Pi.single_apply]

/-- **A unit coordinate shift of a box point**: `x - e_j` written coordinatewise. -/
theorem sub_unitVec2_apply (x : Fin 2 → ℤ) (j i : Fin 2) :
    (x - unitVec2 j) i = x i - (if i = j then 1 else 0) := by
  simp [unitVec2, Pi.single_apply]

/-- **Every cubic box vertex reaches the origin** in the induced lattice graph: by strong induction
on `|x₀| + |x₁|`, step a nonzero coordinate one unit toward `0`, staying in the box. -/
theorem inducedCubicBox_two_reachable_zero (n : ℕ) :
    ∀ (m : ℕ) (x : ↑(cubicBox 2 n)), (x.val 0).natAbs + (x.val 1).natAbs = m →
      (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Reachable x
        ⟨0, zero_mem_cubicBox_two n⟩ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- `m = 0`: both coordinates vanish, so `x = 0`.
      have h0 : (x.val 0).natAbs = 0 := by omega
      have h1 : (x.val 1).natAbs = 0 := by omega
      have hx0 : x.val = 0 := by
        funext i
        fin_cases i
        · exact Int.natAbs_eq_zero.mp h0
        · exact Int.natAbs_eq_zero.mp h1
      rw [show x = ⟨0, zero_mem_cubicBox_two n⟩ from Subtype.ext hx0]
    · -- some coordinate is nonzero; pick `j` and step toward `0`.
      have hxbox := (mem_cubicBox).mp x.property
      obtain ⟨j, hjne⟩ : ∃ j : Fin 2, (x.val j).natAbs ≠ 0 := by
        rcases (by omega : (x.val 0).natAbs ≠ 0 ∨ (x.val 1).natAbs ≠ 0) with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hxj : x.val j ≠ 0 := fun h => hjne (by rw [h]; rfl)
      have hbnd := hxbox j
      rcases lt_or_gt_of_ne hxj with hneg | hpos
      · -- `x.val j < 0`: step `+e_j`
        have hymem : (x.val + unitVec2 j) ∈ cubicBox 2 n := by
          rw [mem_cubicBox]; intro i
          rw [add_unitVec2_apply]
          by_cases hij : i = j
          · subst hij; simp only [↓reduceIte]; omega
          · simp only [if_neg hij, add_zero]; exact hxbox i
        set y : ↑(cubicBox 2 n) := ⟨x.val + unitVec2 j, hymem⟩ with hy
        have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj x y := by
          rw [inducedLattice_adj_iff]
          exact latticeGraph_adj_add_unitVec2 x.val j
        have ey : ∀ i, y.val i = x.val i + (if i = j then 1 else 0) := fun i => by
          rw [hy]; exact add_unitVec2_apply x.val j i
        have hmeas : (y.val 0).natAbs + (y.val 1).natAbs < m := by
          have e0 := ey 0; have e1 := ey 1
          fin_cases j <;> simp_all <;> omega
        exact (hadj.reachable).trans (ih _ hmeas y rfl)
      · -- `x.val j > 0`: step `-e_j`
        have hymem : (x.val - unitVec2 j) ∈ cubicBox 2 n := by
          rw [mem_cubicBox]; intro i
          rw [sub_unitVec2_apply]
          by_cases hij : i = j
          · subst hij; simp only [↓reduceIte]; omega
          · simp only [if_neg hij, sub_zero]; exact hxbox i
        set y : ↑(cubicBox 2 n) := ⟨x.val - unitVec2 j, hymem⟩ with hy
        have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj x y := by
          rw [inducedLattice_adj_iff]
          have hxeq : x.val = y.val + unitVec2 j := by rw [hy]; ring
          rw [hxeq]
          exact (latticeGraph_adj_add_unitVec2 y.val j).symm
        have ey : ∀ i, y.val i = x.val i - (if i = j then 1 else 0) := fun i => by
          rw [hy]; exact sub_unitVec2_apply x.val j i
        have hmeas : (y.val 0).natAbs + (y.val 1).natAbs < m := by
          have e0 := ey 0; have e1 := ey 1
          fin_cases j <;> simp_all <;> omega
        exact (hadj.reachable).trans (ih _ hmeas y rfl)

/-- **The induced 2D cubic box graph is preconnected**: any two vertices of `[-n, n]²` are
connected via the origin. This supplies the `hpre` hypothesis of the Peierls magnetization bound
for the canonical cubic exhaustion. -/
theorem inducedCubicBox_two_preconnected (n : ℕ) :
    (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Preconnected := by
  intro x y
  exact (inducedCubicBox_two_reachable_zero n _ x rfl).trans
    (inducedCubicBox_two_reachable_zero n _ y rfl).symm

/-- **An interior droplet is neighbour-closed**: if every vertex of `S` lies in the strictly smaller
box `[-m, m]²` with `m + 1 ≤ n`, then every lattice neighbour of an `S`-vertex is still a vertex of
`[-n, n]²`. This supplies the `hne` hypothesis of the Peierls magnetization bound for droplets
disjoint from the outer boundary shell. -/
theorem neighbourClosed_of_image_subset_inner {n m : ℕ} (hmn : m + 1 ≤ n)
    {S : Finset ↑(cubicBox 2 n)} (hS : ∀ a ∈ S, a.val ∈ cubicBox 2 m) :
    NeighbourClosed (cubicBox 2 n) S := by
  intro a ha b hadj
  have haval := (mem_cubicBox).mp (hS a ha)
  have hmn' : (m : ℤ) + 1 ≤ n := by exact_mod_cast hmn
  rw [mem_cubicBox]
  intro i
  have hai := haval i
  rcases latticeGraph2_adj_cases hadj with h | h | h | h <;> subst h
  · rw [add_unitVec2_apply]
    have : (0 : ℤ) ≤ (if i = 0 then 1 else 0) ∧ (if i = 0 then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  · rw [sub_unitVec2_apply]
    have : (0 : ℤ) ≤ (if i = 0 then 1 else 0) ∧ (if i = 0 then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  · rw [add_unitVec2_apply]
    have : (0 : ℤ) ≤ (if i = 1 then 1 else 0) ∧ (if i = 1 then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  · rw [sub_unitVec2_apply]
    have : (0 : ℤ) ≤ (if i = 1 then 1 else 0) ∧ (if i = 1 then 1 else 0) ≤ 1 := by
      split <;> omega
    omega

end IsingModel
