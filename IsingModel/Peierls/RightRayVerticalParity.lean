import IsingModel.Peierls.RightRayVerticalStep

/-!
# The vertical parity of the rightward ray (FV §3.7.2)

Combining the vertical-step invariance (`verticalDefect_step`) with a right-end stabilization (the
ray defect vanishes once `x` is to the right of all `B`-edges) gives the vertical analogue of
`rightRayParity_xor_horizontal`: the rightward-ray parity flips between `x` and `x + e₁` iff the
vertical edge `s(x, x+e₁)` lies in `B`. This is the vertical step the fixed-ray region needs.

* `exists_coord0_bound` — `B` being finite, all its edge endpoints have bounded coordinate 0.
* `verticalDefect_eq_zero_of_bound` — far to the right, the vertical defect vanishes.
* `verticalDefect_ray0` — the defect is invariant along the rightward ray (even square count).
* `verticalDefect_eq_zero` — hence the defect vanishes everywhere.
* `rightRayParity_xor_vertical` — the parity flips across `s(x, x+e₁)` iff that edge is in `B`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- **`B`'s endpoints have bounded coordinate 0**: since `B` is finite, there is `M` with every edge
endpoint's coordinate 0 strictly below `M`. -/
theorem exists_coord0_bound (B : Finset (Sym2 (Fin 2 → ℤ))) :
    ∃ M : ℤ, ∀ e ∈ B, ∀ v : Fin 2 → ℤ, v ∈ e → v 0 < M := by
  classical
  obtain ⟨M, hM⟩ := ((B.biUnion (fun e => e.toFinset)).image (fun v => v 0)).bddAbove
  refine ⟨M + 1, fun e he v hv => ?_⟩
  have hvB : v 0 ∈ (B.biUnion (fun e => e.toFinset)).image (fun v => v 0) :=
    Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hv⟩)
  have := hM hvB
  omega

/-- **Far right, no ray edge lies in `B`**: if every `B`-edge endpoint has coordinate 0 below `M`
and `M ≤ x 0`, the ray count from `x` is zero (its edges have coordinate 0 at least `x 0`). -/
theorem rightRayCount_eq_zero_of_bound {B : Finset (Sym2 (Fin 2 → ℤ))} {M : ℤ} {x : Fin 2 → ℤ}
    (hB : ∀ e ∈ B, ∀ v : Fin 2 → ℤ, v ∈ e → v 0 < M) (hx : M ≤ x 0) :
    rightRayCount B x = 0 := by
  classical
  unfold rightRayCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro e he ⟨k, rfl⟩
  have hmem : ray0 x k ∈ (s(ray0 x k, ray0 x (k + 1)) : Sym2 (Fin 2 → ℤ)) :=
    Sym2.mem_iff.mpr (Or.inl rfl)
  have := hB _ he _ hmem
  rw [ray0_apply_zero] at this
  omega

/-- **Far right, the vertical edge is not in `B`**. -/
theorem vertical_edge_notMem_of_bound {B : Finset (Sym2 (Fin 2 → ℤ))} {M : ℤ} {x : Fin 2 → ℤ}
    (hB : ∀ e ∈ B, ∀ v : Fin 2 → ℤ, v ∈ e → v 0 < M) (hx : M ≤ x 0) :
    s(x, x + unitVec2 1) ∉ B := by
  intro hmem
  have := hB _ hmem x (Sym2.mem_iff.mpr (Or.inl rfl))
  omega

/-- **Far right, the vertical defect vanishes**. -/
theorem verticalDefect_eq_zero_of_bound {B : Finset (Sym2 (Fin 2 → ℤ))} {M : ℤ} {x : Fin 2 → ℤ}
    (hB : ∀ e ∈ B, ∀ v : Fin 2 → ℤ, v ∈ e → v 0 < M) (hx : M ≤ x 0) :
    verticalDefect B x = 0 := by
  unfold verticalDefect
  have hx1 : M ≤ (x + unitVec2 1) 0 := by simpa [unitVec2, Pi.add_apply] using hx
  rw [rightRayCount_eq_zero_of_bound hB hx, rightRayCount_eq_zero_of_bound hB hx1,
    if_neg (vertical_edge_notMem_of_bound hB hx)]

/-- **The vertical defect is invariant along the rightward ray** (under the even square count). -/
theorem verticalDefect_ray0 (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ)
    (hSquare : ∀ c : Fin 2 → ℤ,
      Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges c)).card)) (n : ℕ) :
    verticalDefect B x = verticalDefect B (ray0 x n) := by
  induction n with
  | zero => rw [ray0_zero]
  | succ n ih => rw [ih, ray0_succ, verticalDefect_step B (ray0 x n) (hSquare (ray0 x n))]

/-- **The vertical defect vanishes everywhere** (under the even square count). -/
theorem verticalDefect_eq_zero (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ)
    (hSquare : ∀ c : Fin 2 → ℤ,
      Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges c)).card)) :
    verticalDefect B x = 0 := by
  obtain ⟨M, hM⟩ := exists_coord0_bound B
  have hx : M ≤ (ray0 x (M - x 0).toNat) 0 := by
    rw [ray0_apply_zero]; omega
  rw [verticalDefect_ray0 B x hSquare (M - x 0).toNat]
  exact verticalDefect_eq_zero_of_bound hM hx

/-- **Vertical parity flip**: the rightward-ray parity flips between `x` and `x + e₁` iff the edge
`s(x, x+e₁)` lies in `B` (under the even square count). The vertical analogue of
`rightRayParity_xor_horizontal`. -/
theorem rightRayParity_xor_vertical (B : Finset (Sym2 (Fin 2 → ℤ))) (x : Fin 2 → ℤ)
    (hSquare : ∀ c : Fin 2 → ℤ,
      Even ((B.filter (fun e => e ∈ primalSquareBoundaryEdges c)).card)) :
    (Odd (rightRayCount B x) ↔ ¬ Odd (rightRayCount B (x + unitVec2 1))) ↔
      s(x, x + unitVec2 1) ∈ B := by
  have hd := verticalDefect_eq_zero B x hSquare
  unfold verticalDefect at hd
  simp only [Nat.odd_iff]
  by_cases hmem : s(x, x + unitVec2 1) ∈ B
  · rw [if_pos hmem] at hd
    simp only [hmem, iff_true]
    omega
  · rw [if_neg hmem] at hd
    simp only [hmem, iff_false]
    omega

end IsingModel
