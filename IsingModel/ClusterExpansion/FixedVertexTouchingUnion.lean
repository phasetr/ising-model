import IsingModel.ClusterExpansion.TouchingClusterDecomp

/-!
# Coordinate union bound for fixed-vertex touching cluster sequences (GJ §18.4–18.7)

First step of the rooted fixed-vertex Kotecký–Preiss bound (Issue #4230, item D of #4214): the deep
core that bounds the touching-cluster Mayer sum by `κ·|support C|`, volume-uniform.

The touching-cluster sum (`norm_mayerExpansionTermComplex_sub_Gavoid_le`, #4248) ranges over cluster
sequences `ω` for which *some* coordinate's polymer touches `support C`.  To reduce a fixed-vertex
version to a *single-coordinate* (root) sum — the form the existing Penrose/peel machinery bounds —
one first replaces "some coordinate `i` touches `v`" by the union bound over coordinates: the sum
over sequences with `∃ i, v ∈ polymerSupport (ω i)` is at most the sum over coordinates `i` of the
sum over sequences with `v ∈ polymerSupport (ω i)`.

## Main result
* `fixedVertexTouching_termAbsSum_succ_le_sum_coord_rooted` — the coordinate union bound.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7; Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **Coordinate union bound for fixed-vertex touching cluster sequences.**  The absolute Mayer sum
over cluster sequences in which *some* coordinate touches the vertex `v` is bounded by the sum over
coordinates `i` of the absolute Mayer sum over sequences whose `i`-th coordinate touches `v`. -/
theorem fixedVertexTouching_termAbsSum_succ_le_sum_coord_rooted
    (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) (n : ℕ) (z : ℂ) :
    (∑ ω ∈
        (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        ‖(ursellCoefficient ω : ℂ)‖ * ∏ i, ‖z‖ ^ (ω i).card)
      ≤ ∑ i : Fin (n + 1),
        ∑ ω ∈
          (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => v ∈ polymerSupport (ω i)),
          ‖(ursellCoefficient ω : ℂ)‖ * ∏ j, ‖z‖ ^ (ω j).card := by
  classical
  set S := Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G) with hS
  set a : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ :=
    fun ω => ‖(ursellCoefficient ω : ℂ)‖ * ∏ j, ‖z‖ ^ (ω j).card with ha
  have hanonneg : ∀ ω, 0 ≤ a ω := by
    intro ω
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun j _ => by positivity))
  have hcoordnonneg : ∀ ω, 0 ≤ ∑ i : Fin (n + 1), if v ∈ polymerSupport (ω i) then a ω else 0 :=
    fun ω => Finset.sum_nonneg (fun i _ => by split_ifs with h; exacts [hanonneg ω, le_refl 0])
  -- the right-hand side, swapping the order of summation
  have hRHS : (∑ i : Fin (n + 1),
        ∑ ω ∈ S.filter (fun ω => v ∈ polymerSupport (ω i)), a ω)
      = ∑ ω ∈ S, (∑ i : Fin (n + 1), if v ∈ polymerSupport (ω i) then a ω else 0) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  refine le_trans ?_ (ge_of_eq hRHS)
  -- bound termwise on the touching filter, then extend to all of `S`
  refine le_trans (Finset.sum_le_sum (fun ω hω => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => hcoordnonneg ω))
  rw [Finset.mem_filter] at hω
  obtain ⟨i, hi⟩ := hω.2
  calc a ω = if v ∈ polymerSupport (ω i) then a ω else 0 := by rw [if_pos hi]
    _ ≤ ∑ i : Fin (n + 1), if v ∈ polymerSupport (ω i) then a ω else 0 :=
        Finset.single_le_sum
          (f := fun i => if v ∈ polymerSupport (ω i) then a ω else 0)
          (fun k _ => by
            change (0 : ℝ) ≤ if v ∈ polymerSupport (ω k) then a ω else 0
            split_ifs with h; exacts [hanonneg ω, le_refl 0])
          (Finset.mem_univ i)

end IsingModel
