import IsingModel.Peierls.RayExit
import IsingModel.Peierls.RayExitAnchorStep
import IsingModel.Peierls.RayExitAnchorPrefix

/-!
# Crossing parity of a rightward ray (FV §3.7.2)

The fixed-ray region underlying `cutEdges S = B` assigns to each vertex `x` the parity of the number
of `B`-edges on the rightward horizontal ray `ray0 x` (`x, x+e₀, x+2e₀, …`). Since `B` is
finite, only finitely many ray edges lie in `B`, so the count is a finite cardinality.

This file builds the **horizontal step** of that parity: moving the basepoint one step right along
the ray drops exactly the first ray edge `s(x, x+e₀)`, so the parity flips iff that edge lies in
`B`. (The vertical step, which needs the square-boundary telescope, is a later file.)

* `rightRayEdge` — an edge lies on the rightward ray from `x`.
* `rightRayCount` — the number of `B`-edges on the rightward ray from `x`.
* `rightRayCount_eq_first_add_tail` — peel the first ray edge.
* `rightRayParity_xor_horizontal` — the parity flips across `s(x, x+e₀)` iff that edge is in B.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **An edge on the rightward ray from `x`**: it is `s(ray0 x k, ray0 x (k+1))` for some `k`. -/
def rightRayEdge (x : Fin 2 → ℤ) (e : Sym2 (Fin 2 → ℤ)) : Prop :=
  ∃ k : ℕ, e = s(ray0 x k, ray0 x (k + 1))

/-- **Shifting the ray basepoint one step right**: `ray0 (x + e₀) k = ray0 x (k+1)`. -/
theorem ray0_add_unitVec2_zero (x : Fin 2 → ℤ) (k : ℕ) :
    ray0 (x + unitVec2 0) k = ray0 x (k + 1) := by
  rw [← ray0_one x, ray0_add, Nat.add_comm]

/-- **The number of `B`-edges on the rightward ray from `x`**. -/
noncomputable def rightRayCount (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) : ℕ := by
  classical
  exact (B.filter (rightRayEdge x)).card

/-- **A ray edge from `x` is the first edge or a ray edge from `x + e₀`**. -/
theorem rightRayEdge_iff_first_or_tail (x : Fin 2 → ℤ) (e : Sym2 (Fin 2 → ℤ)) :
    rightRayEdge x e ↔ e = s(x, x + unitVec2 0) ∨ rightRayEdge (x + unitVec2 0) e := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact Or.inl (by rw [ray0_zero, ray0_one])
    | succ k => exact Or.inr ⟨k, by rw [ray0_add_unitVec2_zero, ray0_add_unitVec2_zero]⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨0, by rw [ray0_zero, ray0_one]⟩
    · exact ⟨k + 1, by rw [ray0_add_unitVec2_zero, ray0_add_unitVec2_zero]⟩

/-- **The first ray edge is not a ray edge from `x + e₀`**: `s(x, x+e₀)` does not lie on the ray
starting at `x + e₀` (its endpoints `ray0 x 0, ray0 x 1` are strictly left of that ray, by
injectivity of `ray0`). -/
theorem not_rightRayEdge_tail_first (x : Fin 2 → ℤ) :
    ¬ rightRayEdge (x + unitVec2 0) (s(x, x + unitVec2 0)) := by
  rintro ⟨k, hk⟩
  rw [ray0_add_unitVec2_zero, ray0_add_unitVec2_zero] at hk
  rw [show (s(x, x + unitVec2 0) : Sym2 (Fin 2 → ℤ)) = s(ray0 x 0, ray0 x 1) by
    rw [ray0_zero, ray0_one]] at hk
  rw [Sym2.eq_iff] at hk
  rcases hk with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact (Nat.succ_ne_zero k) (ray0_injective x h1.symm)
  · exact (Nat.succ_ne_zero (k + 1)) (ray0_injective x h1.symm)

/-- **Peeling the first ray edge**: the ray count from `x` is `1` (if the first edge `s(x, x+e₀)`
lies in `B`) plus the ray count from `x + e₀`. -/
theorem rightRayCount_eq_first_add_tail (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) :
    rightRayCount B x =
      (if s(x, x + unitVec2 0) ∈ B then 1 else 0) + rightRayCount B (x + unitVec2 0) := by
  classical
  unfold rightRayCount
  have hsplit : B.filter (rightRayEdge x) =
      B.filter (fun e => e = s(x, x + unitVec2 0)) ∪
        B.filter (rightRayEdge (x + unitVec2 0)) := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr fun e _ => by rw [rightRayEdge_iff_first_or_tail]
  have hdisj : Disjoint (B.filter (fun e => e = s(x, x + unitVec2 0)))
      (B.filter (rightRayEdge (x + unitVec2 0))) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [Finset.mem_filter] at he₁ he₂
    rw [he₁.2] at he₂
    exact not_rightRayEdge_tail_first x he₂.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.filter_eq']
  by_cases hmem : s(x, x + unitVec2 0) ∈ B <;> simp [hmem]

/-- **Horizontal parity flip**: the rightward-ray parity flips between `x` and `x + e₀` iff the
edge `s(x, x+e₀)` lies in `B`. -/
theorem rightRayParity_xor_horizontal (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) :
    (Odd (rightRayCount B x) ↔ ¬ Odd (rightRayCount B (x + unitVec2 0))) ↔
      s(x, x + unitVec2 0) ∈ B := by
  rw [rightRayCount_eq_first_add_tail]
  by_cases hmem : s(x, x + unitVec2 0) ∈ B <;>
    simp only [hmem, if_true, if_false, iff_true, iff_false, Nat.odd_iff] <;> omega

end IsingModel
