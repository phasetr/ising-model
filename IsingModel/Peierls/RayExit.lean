import IsingModel.Peierls.DartOfCut

/-!
# The axis ray exits a finite region (FV §3.7.2)

The Peierls anchor argument fixes a reference site `i` and walks along the `+e₀` ray
`ray0 i k = i + k·e₀`. A finite region `F` containing `i` is eventually left by the ray, so there is
a *first exit* index `k` with `ray0 i k ∈ F` and `ray0 i (k+1) ∉ F`. The exit edge
`{ray0 i k, ray0 i (k+1)}` is a cut edge, providing the anchor that pins the contour to the fixed
sequence `z_k = ray0 i k`.

* `ray0`, `ray0_zero`, `ray0_succ`, `ray0_injective`, `ray0_adj_succ` — the ray.
* `exists_first_exit` — a finite region containing `i` has a first exit along the ray.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The `+e₀` **axis ray** from `i`: `ray0 i k = i + k·e₀`. -/
def ray0 (i : Fin 2 → ℤ) (k : ℕ) : Fin 2 → ℤ := i + (k : ℤ) • unitVec2 0

/-- The ray starts at `i`. -/
@[simp] theorem ray0_zero (i : Fin 2 → ℤ) : ray0 i 0 = i := by
  simp [ray0]

/-- The ray steps by `e₀`. -/
theorem ray0_succ (i : Fin 2 → ℤ) (k : ℕ) : ray0 i (k + 1) = ray0 i k + unitVec2 0 := by
  simp only [ray0, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  ring

/-- The zeroth coordinate of the ray is `i 0 + k`. -/
theorem ray0_apply_zero (i : Fin 2 → ℤ) (k : ℕ) : ray0 i k 0 = i 0 + (k : ℤ) := by
  simp [ray0, unitVec2]

/-- The ray is injective in the step count. -/
theorem ray0_injective (i : Fin 2 → ℤ) : Function.Injective (ray0 i) := by
  intro j k hjk
  have := congrFun hjk 0
  rw [ray0_apply_zero, ray0_apply_zero] at this
  exact_mod_cast (add_left_cancel this)

/-- Consecutive ray points are lattice-adjacent. -/
theorem ray0_adj_succ (i : Fin 2 → ℤ) (k : ℕ) :
    (latticeGraph 2).Adj (ray0 i k) (ray0 i (k + 1)) := by
  rw [ray0_succ]
  change (∑ j : Fin 2, |ray0 i k j - (ray0 i k + unitVec2 0) j|) = 1
  rw [Fin.sum_univ_two]
  simp [unitVec2, Pi.add_apply]

/-- **A finite region containing `i` has a first exit along the ray**: there is `k` with
`ray0 i k ∈ F` and `ray0 i (k+1) ∉ F`. -/
theorem exists_first_exit {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} (hi : i ∈ F) :
    ∃ k, ray0 i k ∈ F ∧ ray0 i (k + 1) ∉ F := by
  classical
  have hex : ∃ k, ray0 i k ∉ F := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hinf : (↑F : Set (Fin 2 → ℤ)).Infinite :=
      Set.infinite_of_injective_forall_mem (ray0_injective i) (fun k => h k)
    exact (F.finite_toSet).not_infinite hinf
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, ray0_zero] at this
    exact this hi
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · -- the point just before the first non-membership is still in `F`
    by_contra hkF
    have hle := Nat.find_min' hex hkF
    omega
  · have hk : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hk]
    exact Nat.find_spec hex

end IsingModel
