import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LinearBrick
import IsingModel.Concrete.StripeBrick2D

/-!
# Slab brick split — slab geometry, cardinality, and shift identities

Part of the split slab-brick free-energy layer (Issue #1850).
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

/-- **General `d+1`-dim slab** on `Fin (d+1) → ℤ`: rectangular block
`[0, n) × [0, widths 0) × … × [0, widths (d-1))`. Coord 0 is the
growing Fekete direction; coords `1..d` are the fixed cross-section
specified by `widths : Fin d → ℕ`. -/
noncomputable def slabBrick (widths : Fin d → ℕ) (n : ℕ) :
    Finset (Fin (d + 1) → ℤ) :=
  Fintype.piFinset (fun i : Fin (d + 1) =>
    Finset.Ico (0 : ℤ)
      (Fin.cases (n : ℤ) (fun j : Fin d => (widths j : ℤ)) i))

/-- **Cardinality of `slabBrick widths n`** equals `n · ∏ j, widths j`. -/
theorem slabBrick_card (widths : Fin d → ℕ) (n : ℕ) :
    (slabBrick widths n).card = n * ∏ j : Fin d, widths j := by
  unfold slabBrick
  rw [Fintype.card_piFinset]
  -- `∏ i : Fin (d+1), (Ico 0 (Fin.cases n widths i)).card`
  -- Split via `Fin.prod_univ_succ`: `f 0 * ∏ j, f j.succ`.
  rw [Fin.prod_univ_succ]
  simp [Int.card_Ico, Fin.cases_zero, Fin.cases_succ]

/-- **Additive cardinality in the length parameter**:
`|slabBrick widths (m + n)| = |slabBrick widths m| + |slabBrick widths n|`.
Foundation for the `hcard_add` hypothesis of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive`. -/
theorem slabBrick_card_add (widths : Fin d → ℕ) (m n : ℕ) :
    (slabBrick widths (m + n)).card
      = (slabBrick widths m).card + (slabBrick widths n).card := by
  rw [slabBrick_card, slabBrick_card, slabBrick_card]
  ring

/-- **Non-degeneracy of the base step**:
`|slabBrick widths 1| = ∏ widths j ≠ 0` provided every `widths j ≠ 0`. -/
theorem slabBrick_one_card_ne_zero {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0) :
    (slabBrick widths 1).card ≠ 0 := by
  rw [slabBrick_card, one_mul]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hw j)

/-- **Membership characterisation**: `v ∈ slabBrick widths n ↔
∀ i, 0 ≤ v i ∧ v i < Fin.cases (n:ℤ) widths i`. -/
theorem mem_slabBrick {widths : Fin d → ℕ} {n : ℕ} {v : Fin (d + 1) → ℤ} :
    v ∈ slabBrick widths n
      ↔ (0 ≤ v 0 ∧ v 0 < (n : ℤ)) ∧
          ∀ j : Fin d, 0 ≤ v j.succ ∧ v j.succ < (widths j : ℤ) := by
  unfold slabBrick
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
    · simp [Finset.mem_Ico, hv0a, hv0b]
    · intro j
      simp only [Fin.cases_succ, Finset.mem_Ico]
      exact hj j

/-- **Coord-0 shift vector** on `Fin (d+1) → ℤ` by `(m : ℤ)`:
zero in all coords except coord 0, which equals `m`. -/
noncomputable def shiftCoord0 (m : ℕ) : Fin (d + 1) → ℤ :=
  Fin.cases (m : ℤ) (fun _ : Fin d => (0 : ℤ))

@[simp]
private theorem shiftCoord0_zero (m : ℕ) : (shiftCoord0 (d := d) m) 0 = (m : ℤ) := by
  unfold shiftCoord0
  rfl

@[simp]
private theorem shiftCoord0_succ (m : ℕ) (j : Fin d) :
    (shiftCoord0 (d := d) m) j.succ = 0 := by
  unfold shiftCoord0
  rfl

/-- **Disjointness of shifted slabs**: `slabBrick widths m` and the
`m`-shift of `slabBrick widths n` along coord 0 are disjoint. -/
theorem slabBrick_disjoint_shift (widths : Fin d → ℕ) (m n : ℕ) :
    Disjoint (slabBrick widths m)
      (Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n)) := by
  rw [Finset.disjoint_left]
  intro v hvm hvs
  rw [Ambient.mem_vaddFinset] at hvs
  obtain ⟨u, hu, huv⟩ := hvs
  rw [mem_slabBrick] at hvm hu
  have hv0 : v 0 = (m : ℤ) + u 0 := by
    have : (shiftCoord0 (d := d) m +ᵥ u) 0 = v 0 := congrArg (· 0) huv
    simp [vadd_eq_add] at this
    linarith
  -- `hvm.1.2 : v 0 < m` but `hv0 : v 0 = m + u 0 ≥ m` (since `hu.1.1 : 0 ≤ u 0`).
  have := hvm.1.2
  have := hu.1.1
  omega

/-- **Union decomposition** on coord 0:
`slabBrick widths m ∪ (coord-0-shift_m +ᵥ slabBrick widths n)
  = slabBrick widths (m + n)`. -/
theorem slabBrick_union_shift (widths : Fin d → ℕ) (m n : ℕ) :
    slabBrick widths m ∪
        Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n)
      = slabBrick widths (m + n) := by
  ext v
  simp only [Finset.mem_union, Ambient.mem_vaddFinset, mem_slabBrick]
  constructor
  · rintro (⟨⟨h0a, h0b⟩, hj⟩ | ⟨u, ⟨⟨hu0a, hu0b⟩, huj⟩, huv⟩)
    · refine ⟨⟨h0a, ?_⟩, hj⟩
      have hmn : (m : ℤ) ≤ (m + n : ℕ) := by push_cast; linarith
      exact lt_of_lt_of_le h0b hmn
    · -- `huv : shift +ᵥ u = v`, so `v 0 = m + u 0` and `v j.succ = u j.succ`.
      have hv0 : v 0 = (m : ℤ) + u 0 := by
        have : (shiftCoord0 (d := d) m +ᵥ u) 0 = v 0 := congrArg (· 0) huv
        simp [vadd_eq_add] at this
        linarith
      have hvj : ∀ j : Fin d, v j.succ = u j.succ := by
        intro j
        have : (shiftCoord0 (d := d) m +ᵥ u) j.succ = v j.succ :=
          congrArg (· j.succ) huv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · rw [hv0]; linarith
      · rw [hv0]; push_cast; linarith
      · rw [hvj j]; exact huj j
  · rintro ⟨⟨h0a, h0b⟩, hj⟩
    by_cases hcase : v 0 < (m : ℤ)
    · left; exact ⟨⟨h0a, hcase⟩, hj⟩
    · right
      push Not at hcase
      refine ⟨(Fin.cases (v 0 - (m : ℤ)) (fun j : Fin d => v j.succ)
                : Fin (d + 1) → ℤ),
        ⟨⟨?_, ?_⟩, fun j => ?_⟩, ?_⟩
      · simp only [Fin.cases_zero]; linarith
      · simp only [Fin.cases_zero]; push_cast at h0b; linarith
      · simp only [Fin.cases_succ]; exact hj j
      · funext i
        refine Fin.cases ?_ ?_ i
        · -- Coord 0: `m + (v 0 - m) = v 0`.
          change ((shiftCoord0 (d := d) m) +ᵥ
              (Fin.cases (v 0 - (m : ℤ)) (fun j : Fin d => v j.succ)
                : Fin (d + 1) → ℤ)) 0 = v 0
          simp only [shiftCoord0_zero, Fin.cases_zero, vadd_eq_add,
            Pi.add_apply]
          linarith
        · intro j
          -- Coord j.succ: `0 + v j.succ = v j.succ`.
          change ((shiftCoord0 (d := d) m) +ᵥ
              (Fin.cases (v 0 - (m : ℤ)) (fun k : Fin d => v k.succ)
                : Fin (d + 1) → ℤ)) j.succ = v j.succ
          simp only [shiftCoord0_succ, Fin.cases_succ, vadd_eq_add,
            Pi.add_apply, zero_add]


end Concrete

end IsingModel
