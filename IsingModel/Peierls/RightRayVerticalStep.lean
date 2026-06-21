import IsingModel.Peierls.RightRayParity
import IsingModel.Peierls.RightRayVerticalXor

/-!
# The vertical-step invariance of the ray defect (FV §3.7.2)

The fixed-ray region's vertical step needs that, moving one column right, the "vertical defect"
`(rightRayCount B x + rightRayCount B (x+e₁) + ⟦s(x,x+e₁) ∈ B⟧) mod 2` is invariant. This is
unit-square cancellation: the defect difference between columns `x` and `x+e₀` is the mod-2 sum of
the four sides of the unit square at `x` (the two horizontal rays' first edges, the left vertical
edge, and the right vertical edge), which is even by `unitSquare_sides_even`.

* `rightRayParity_horizontal_mod2` — the mod-2 horizontal parity: `count x + count(x+e₀) +
  ⟦s(x,x+e₀) ∈ B⟧` is even.
* `verticalDefect` — the mod-2 vertical defect at `x`.
* `verticalDefect_step` — the defect is invariant under `x ↦ x + e₀` (even square count).

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **Mod-2 horizontal parity**: `count x + count(x+e₀) + ⟦s(x,x+e₀) ∈ B⟧` is even, the
additive form of `rightRayParity_xor_horizontal`. -/
theorem rightRayParity_horizontal_mod2 (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) :
    (rightRayCount B x + rightRayCount B (x + unitVec2 0) +
      (if s(x, x + unitVec2 0) ∈ B then 1 else 0)) % 2 = 0 := by
  have h := rightRayParity_xor_horizontal B x
  simp only [Nat.odd_iff] at h
  by_cases hmem : s(x, x + unitVec2 0) ∈ B
  · rw [if_pos hmem]
    simp only [hmem, iff_true] at h
    omega
  · rw [if_neg hmem]
    simp only [hmem, iff_false] at h
    omega

/-- **The mod-2 vertical defect at `x`**: `(count x + count(x+e₁) + ⟦s(x,x+e₁) ∈ B⟧) mod 2`.
The fixed-ray region uses this defect; the goal is that it is `0`. -/
noncomputable def verticalDefect (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ) : ℕ :=
  (rightRayCount B x + rightRayCount B (x + unitVec2 1) +
    (if s(x, x + unitVec2 1) ∈ B then 1 else 0)) % 2

/-- **The vertical defect is invariant under a rightward step** (under the even square count): the
defect at `x` equals the defect at `x + e₀`. The difference is the mod-2 sum of the four sides of
the unit square at `x`, even by `unitSquare_sides_even`. -/
theorem verticalDefect_step (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ)
    (hSq : Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges x)).card)) :
    verticalDefect B x = verticalDefect B (x + unitVec2 0) := by
  have hbot := rightRayParity_horizontal_mod2 B x
  have htop := rightRayParity_horizontal_mod2 B (x + unitVec2 1)
  have hsq := unitSquare_sides_even B x hSq
  rw [Nat.even_iff] at hsq
  -- Normalise the top-right corner `x+e₁+e₀` to `x+e₀+e₁` so all counts/edges share atoms.
  have hcomm : x + unitVec2 1 + unitVec2 0 = x + unitVec2 0 + unitVec2 1 := by abel
  rw [hcomm] at hsq htop
  unfold verticalDefect
  -- now everything is in terms of the four side indicators and the four ray counts; omega closes.
  omega

end IsingModel
