import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LinearBrick
import IsingModel.Concrete.SlabBrick
import IsingModel.Concrete.StripeBrick2D

/-!
# Centered slab split — slab geometry, cardinality, and shift identities

Part of the split `IsingModel.Concrete.CenteredSlab` development.
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

/-- **Two-sided centered slab** on `Fin (d+1) → ℤ`: rectangular block
`[-n, n) × [0, widths 0) × … × [0, widths (d-1))`, centered at the
origin on coord 0. Cardinality is `2n · ∏ widths j`, linear in `n`. -/
noncomputable def centeredSlab (widths : Fin d → ℕ) (n : ℕ) :
    Finset (Fin (d + 1) → ℤ) :=
  Fintype.piFinset (fun i : Fin (d + 1) =>
    Fin.cases
      (Finset.Ico (-(n : ℤ)) (n : ℤ))
      (fun j : Fin d => Finset.Ico (0 : ℤ) (widths j : ℤ))
      i)

/-- **Cardinality of `centeredSlab widths n`** equals `2n · ∏ widths j`. -/
theorem centeredSlab_card (widths : Fin d → ℕ) (n : ℕ) :
    (centeredSlab widths n).card = 2 * n * ∏ j : Fin d, widths j := by
  unfold centeredSlab
  rw [Fintype.card_piFinset, Fin.prod_univ_succ, Fin.cases_zero]
  have hj : ∀ j : Fin d, ((fun j : Fin d => Finset.Ico (0 : ℤ) (widths j : ℤ)) j).card
      = widths j := by
    intro j
    simp only [Int.card_Ico]
    omega
  have h0 : (Finset.Ico (-(n : ℤ)) (n : ℤ)).card = 2 * n := by
    rw [Int.card_Ico]
    omega
  simp only [Fin.cases_succ]
  rw [h0]
  simp [hj]

/-- **Additive cardinality in `n`**:
`|centeredSlab widths (m + n)| = |centeredSlab widths m| + |centeredSlab widths n|`. -/
theorem centeredSlab_card_add (widths : Fin d → ℕ) (m n : ℕ) :
    (centeredSlab widths (m + n)).card
      = (centeredSlab widths m).card + (centeredSlab widths n).card := by
  rw [centeredSlab_card, centeredSlab_card, centeredSlab_card]
  ring

/-- **Non-degeneracy of the base step**:
`|centeredSlab widths 1| = 2 · ∏ widths j ≠ 0` provided every `widths j ≠ 0`. -/
theorem centeredSlab_one_card_ne_zero {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0) :
    (centeredSlab widths 1).card ≠ 0 := by
  rw [centeredSlab_card]
  have h2 : (2 : ℕ) ≠ 0 := by decide
  have hprod : (∏ j : Fin d, widths j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hw j)
  simp [h2, hprod]

/-- **Membership characterisation**: `v ∈ centeredSlab widths n ↔
(-n ≤ v 0 < n) ∧ ∀ j, 0 ≤ v j.succ < widths j`. -/
theorem mem_centeredSlab {widths : Fin d → ℕ} {n : ℕ} {v : Fin (d + 1) → ℤ} :
    v ∈ centeredSlab widths n
      ↔ (-(n : ℤ) ≤ v 0 ∧ v 0 < (n : ℤ)) ∧
          ∀ j : Fin d, 0 ≤ v j.succ ∧ v j.succ < (widths j : ℤ) := by
  unfold centeredSlab
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · have h0 := h 0
      simp only [Fin.cases_zero, Finset.mem_Ico] at h0
      exact h0
    · have hj := h j.succ
      simp only [Fin.cases_succ, Finset.mem_Ico] at hj
      exact hj
  · rintro ⟨⟨hv0a, hv0b⟩, hj⟩ i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cases_zero, Finset.mem_Ico]
      exact ⟨hv0a, hv0b⟩
    · intro j
      simp only [Fin.cases_succ, Finset.mem_Ico]
      exact hj j

/-- **Coord-0 shift vector** on `Fin (d+1) → ℤ` by integer `k`:
zero in all coords except coord 0, which equals `k`. -/
noncomputable def shiftCoord0Int (k : ℤ) : Fin (d + 1) → ℤ :=
  Fin.cases k (fun _ : Fin d => (0 : ℤ))

@[simp]
theorem shiftCoord0Int_zero (k : ℤ) :
    (shiftCoord0Int (d := d) k) 0 = k := by
  unfold shiftCoord0Int; rfl

@[simp]
theorem shiftCoord0Int_succ (k : ℤ) (j : Fin d) :
    (shiftCoord0Int (d := d) k) j.succ = 0 := by
  unfold shiftCoord0Int; rfl

/-- **Disjointness of double-shifted centered slabs**:
`shift_(-n) (centeredSlab widths m)` and `shift_m (centeredSlab widths n)`
are disjoint (they meet at the midpoint `m - n` on coord 0). -/
theorem centeredSlab_disjoint_double_shift (widths : Fin d → ℕ) (m n : ℕ) :
    Disjoint
      (Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
        (centeredSlab widths m))
      (Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
        (centeredSlab widths n)) := by
  rw [Finset.disjoint_left]
  intro v hvm hvs
  rw [Ambient.mem_vaddFinset] at hvm hvs
  obtain ⟨u, hu, huv⟩ := hvm
  obtain ⟨w, hw, hwv⟩ := hvs
  rw [mem_centeredSlab] at hu hw
  -- `huv : shift_(-n) +ᵥ u = v`, so `v 0 = -n + u 0`.
  have hv0_left : v 0 = -(n : ℤ) + u 0 := by
    have : (shiftCoord0Int (d := d) (-(n : ℤ)) +ᵥ u) 0 = v 0 :=
      congrArg (· 0) huv
    simp [vadd_eq_add] at this
    linarith
  -- `hwv : shift_m +ᵥ w = v`, so `v 0 = m + w 0`.
  have hv0_right : v 0 = (m : ℤ) + w 0 := by
    have : (shiftCoord0Int (d := d) (m : ℤ) +ᵥ w) 0 = v 0 :=
      congrArg (· 0) hwv
    simp [vadd_eq_add] at this
    linarith
  -- From `u 0 < m` (hu.1.2) and `v 0 = -n + u 0`, we get `v 0 < m - n`.
  -- From `w 0 ≥ -n` (hw.1.1) and `v 0 = m + w 0`, we get `v 0 ≥ m - n`.
  have hu0 := hu.1.2
  have hw0 := hw.1.1
  linarith

/-- **Union decomposition** on coord 0:
`shift_(-n) (centeredSlab widths m) ∪ shift_m (centeredSlab widths n)
  = centeredSlab widths (m + n)`.

Corresponds to the interval identity
`[-m-n, m-n) ∪ [m-n, m+n) = [-m-n, m+n)` on coord 0, with coords
`1..d` unchanged. -/
theorem centeredSlab_union_double_shift (widths : Fin d → ℕ) (m n : ℕ) :
    Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
        (centeredSlab widths m)
      ∪ Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
        (centeredSlab widths n)
      = centeredSlab widths (m + n) := by
  ext v
  simp only [Finset.mem_union, Ambient.mem_vaddFinset, mem_centeredSlab]
  constructor
  · rintro (⟨u, ⟨⟨hu0a, hu0b⟩, huj⟩, huv⟩ |
             ⟨w, ⟨⟨hw0a, hw0b⟩, hwj⟩, hwv⟩)
    · -- `u 0 ∈ [-m, m)`, `v 0 = -n + u 0`, so `v 0 ∈ [-m-n, m-n) ⊂ [-m-n, m+n)`.
      have hv0 : v 0 = -(n : ℤ) + u 0 := by
        have : (shiftCoord0Int (d := d) (-(n : ℤ)) +ᵥ u) 0 = v 0 :=
          congrArg (· 0) huv
        simp [vadd_eq_add] at this
        linarith
      have hvj : ∀ j : Fin d, v j.succ = u j.succ := by
        intro j
        have : (shiftCoord0Int (d := d) (-(n : ℤ)) +ᵥ u) j.succ = v j.succ :=
          congrArg (· j.succ) huv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · rw [hv0]; push_cast; linarith
      · rw [hv0]; push_cast; linarith
      · rw [hvj j]; exact huj j
    · -- `w 0 ∈ [-n, n)`, `v 0 = m + w 0`, so `v 0 ∈ [m-n, m+n) ⊂ [-m-n, m+n)`.
      have hv0 : v 0 = (m : ℤ) + w 0 := by
        have : (shiftCoord0Int (d := d) (m : ℤ) +ᵥ w) 0 = v 0 :=
          congrArg (· 0) hwv
        simp [vadd_eq_add] at this
        linarith
      have hvj : ∀ j : Fin d, v j.succ = w j.succ := by
        intro j
        have : (shiftCoord0Int (d := d) (m : ℤ) +ᵥ w) j.succ = v j.succ :=
          congrArg (· j.succ) hwv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · rw [hv0]; push_cast; linarith
      · rw [hv0]; push_cast; linarith
      · rw [hvj j]; exact hwj j
  · rintro ⟨⟨h0a, h0b⟩, hj⟩
    by_cases hcase : v 0 < (m : ℤ) - (n : ℤ)
    · -- Left piece: construct `u : Fin (d+1) → ℤ` with `u 0 = v 0 + n` (∈ [-m, m))
      -- and `u j.succ = v j.succ`.
      left
      refine ⟨(Fin.cases (v 0 + (n : ℤ))
                (fun j : Fin d => v j.succ) : Fin (d + 1) → ℤ),
        ⟨⟨?_, ?_⟩, fun j => ?_⟩, ?_⟩
      · simp only [Fin.cases_zero]
        push_cast at h0a
        linarith
      · simp only [Fin.cases_zero]
        linarith
      · simp only [Fin.cases_succ]; exact hj j
      · funext i
        refine Fin.cases ?_ ?_ i
        · change ((shiftCoord0Int (d := d) (-(n : ℤ))) +ᵥ
              (Fin.cases (v 0 + (n : ℤ)) (fun j : Fin d => v j.succ)
                : Fin (d + 1) → ℤ)) 0 = v 0
          simp only [shiftCoord0Int_zero, Fin.cases_zero, vadd_eq_add,
            Pi.add_apply]
          linarith
        · intro j
          change ((shiftCoord0Int (d := d) (-(n : ℤ))) +ᵥ
              (Fin.cases (v 0 + (n : ℤ)) (fun k : Fin d => v k.succ)
                : Fin (d + 1) → ℤ)) j.succ = v j.succ
          simp only [shiftCoord0Int_succ, Fin.cases_succ, vadd_eq_add,
            Pi.add_apply, zero_add]
    · -- Right piece: construct `w` with `w 0 = v 0 - m` (∈ [-n, n)).
      push Not at hcase
      right
      refine ⟨(Fin.cases (v 0 - (m : ℤ))
                (fun j : Fin d => v j.succ) : Fin (d + 1) → ℤ),
        ⟨⟨?_, ?_⟩, fun j => ?_⟩, ?_⟩
      · simp only [Fin.cases_zero]
        linarith
      · simp only [Fin.cases_zero]
        push_cast at h0b
        linarith
      · simp only [Fin.cases_succ]; exact hj j
      · funext i
        refine Fin.cases ?_ ?_ i
        · change ((shiftCoord0Int (d := d) (m : ℤ)) +ᵥ
              (Fin.cases (v 0 - (m : ℤ)) (fun j : Fin d => v j.succ)
                : Fin (d + 1) → ℤ)) 0 = v 0
          simp only [shiftCoord0Int_zero, Fin.cases_zero, vadd_eq_add,
            Pi.add_apply]
          linarith
        · intro j
          change ((shiftCoord0Int (d := d) (m : ℤ)) +ᵥ
              (Fin.cases (v 0 - (m : ℤ)) (fun k : Fin d => v k.succ)
                : Fin (d + 1) → ℤ)) j.succ = v j.succ
          simp only [shiftCoord0Int_succ, Fin.cases_succ, vadd_eq_add,
            Pi.add_apply, zero_add]


end Concrete

end IsingModel
