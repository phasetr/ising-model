import IsingModel.Peierls.RayExit
import IsingModel.Peierls.DartDualCutCard

/-!
# The ray first-exit distance is bounded by the cut size (FV §3.7.2)

The `+e₀`-ray first-exit distance `k` is strictly less than the dual cut size `r = |dartDualCut F|`,
*without* using contour connectivity. At the first exit, `ray0 i 0, …, ray0 i k` all lie in `F`;
from each `ray0 i t` shoot a `+e₁` ray, whose own first exit gives a boundary dart with tail at
`x`-coordinate `i₀ + t`. These `k+1` darts are distinct (different tail `x`-coordinate), so
`k + 1 ≤ |BoundaryDart F| = |dartDualCut F|`. This bounds the Peierls ray anchors to the fixed
sequence `z_0, …, z_r`, making the contour count volume-independent.

* `ray1`, `exists_first_exit_ray1`, `exists_e1_exit_dart` — the `+e₁` exit dart.
* `exists_first_exit_below` — the strengthened first exit (all earlier points in `F`).
* `firstExit_lt_dartDualCut_card` — the bound `k < r`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

/-- The `+e₁` **axis ray** from `p`. -/
def ray1 (p : Fin 2 → ℤ) (k : ℕ) : Fin 2 → ℤ := p + (k : ℤ) • unitVec2 1

/-- The `+e₁` ray steps by `e₁`. -/
theorem ray1_succ (p : Fin 2 → ℤ) (k : ℕ) : ray1 p (k + 1) = ray1 p k + unitVec2 1 := by
  simp only [ray1, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  ring

/-- The `+e₁` ray fixes the zeroth coordinate. -/
theorem ray1_apply_zero (p : Fin 2 → ℤ) (k : ℕ) : ray1 p k 0 = p 0 := by
  simp [ray1, unitVec2]

/-- The first coordinate of the `+e₁` ray is `p 1 + k`. -/
theorem ray1_apply_one (p : Fin 2 → ℤ) (k : ℕ) : ray1 p k 1 = p 1 + (k : ℤ) := by
  simp [ray1, unitVec2]

/-- The `+e₁` ray is injective in the step count. -/
theorem ray1_injective (p : Fin 2 → ℤ) : Function.Injective (ray1 p) := by
  intro j k hjk
  have := congrFun hjk 1
  rw [ray1_apply_one, ray1_apply_one] at this
  exact_mod_cast (add_left_cancel this)

/-- A finite region containing `p` has a first exit along the `+e₁` ray. -/
theorem exists_first_exit_ray1 {F : Finset (Fin 2 → ℤ)} {p : Fin 2 → ℤ} (hp : p ∈ F) :
    ∃ s, ray1 p s ∈ F ∧ ray1 p (s + 1) ∉ F := by
  classical
  have hex : ∃ s, ray1 p s ∉ F := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hinf : (↑F : Set (Fin 2 → ℤ)).Infinite :=
      Set.infinite_of_injective_forall_mem (ray1_injective p) (fun s => h s)
    exact (F.finite_toSet).not_infinite hinf
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp only [ray1, Nat.cast_zero, zero_smul, add_zero] at this
    exact this hp
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · by_contra hsF
    have := Nat.find_min' hex hsF
    omega
  · have hk : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hk]
    exact Nat.find_spec hex

/-- **The `+e₁` exit dart**: at a `+e₁` exit point `q`, the dart `tail = q`, `dir = e₁` is valid. -/
theorem exists_e1_exit_dart {F : Finset (Fin 2 → ℤ)} {q : Fin 2 → ℤ}
    (hq : q ∈ F) (hq' : q + unitVec2 1 ∉ F) :
    ∃ d : BoundaryDart F, d.tail = q := by
  have hL : leftSite q 2 = q := by simp [leftSite, unitVec2]
  have hR : rightSite q 2 = q + unitVec2 1 := by
    funext j; fin_cases j <;> simp [rightSite, leftSite, Dir2.turnLeft, Dir2.vec, unitVec2,
      Pi.add_apply, Pi.sub_apply]
  exact ⟨⟨q, 2, by rw [hL]; exact hq, by rw [hR]; exact hq'⟩, rfl⟩

/-- **The strengthened first exit**: there is `k` with all `ray0 i t` (`t ≤ k`) in `F` and
`ray0 i (k+1) ∉ F`. -/
theorem exists_first_exit_below {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} (hi : i ∈ F) :
    ∃ k, (∀ t, t ≤ k → ray0 i t ∈ F) ∧ ray0 i (k + 1) ∉ F := by
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
  · intro t ht
    by_contra htF
    have := Nat.find_min' hex htF
    omega
  · have hk : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hk]
    exact Nat.find_spec hex

/-- A boundary dart whose tail sits at `x`-coordinate `i₀ + t`, obtained by the `+e₁` exit from
`ray0 i t`. -/
theorem exists_tail_at {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {t : ℕ}
    (ht : ray0 i t ∈ F) : ∃ d : BoundaryDart F, d.tail 0 = i 0 + (t : ℤ) := by
  obtain ⟨s, hs1, hs2⟩ := exists_first_exit_ray1 ht
  rw [ray1_succ] at hs2
  obtain ⟨d, hd⟩ := exists_e1_exit_dart hs1 hs2
  refine ⟨d, ?_⟩
  rw [hd, ray1_apply_zero, ray0_apply_zero]

/-- **The first-exit distance is bounded by the cut size**: `k < |dartDualCut F|`. -/
theorem firstExit_lt_dartDualCut_card {F : Finset (Fin 2 → ℤ)} {i : Fin 2 → ℤ} {k : ℕ}
    (hbelow : ∀ t, t ≤ k → ray0 i t ∈ F) : k < (dartDualCut F).card := by
  classical
  have hchoose : ∀ t : Fin (k + 1), ∃ d : BoundaryDart F, d.tail 0 = i 0 + (t : ℤ) :=
    fun t => exists_tail_at (hbelow t (by omega))
  let f : Fin (k + 1) → BoundaryDart F := fun t => (hchoose t).choose
  have hf : ∀ t, (f t).tail 0 = i 0 + (t : ℤ) := fun t => (hchoose t).choose_spec
  have hinj : Function.Injective f := by
    intro t t' htt
    have h0 : (f t).tail 0 = (f t').tail 0 := by rw [htt]
    rw [hf, hf] at h0
    have : (t : ℤ) = (t' : ℤ) := add_left_cancel h0
    exact Fin.ext (by exact_mod_cast this)
  have hcard : k + 1 ≤ Fintype.card (BoundaryDart F) := by
    have := Fintype.card_le_of_injective f hinj
    simpa using this
  rw [dartDualCut_card, Finset.card_univ]
  omega

end IsingModel
