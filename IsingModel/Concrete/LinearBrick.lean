import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum

/-!
# 1D linear brick on `latticeGraph 1` (§4.6 Prop 4.6.1 concrete ℤ instance)

Concrete application of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive` (PR #638) to
the 1D linear-brick exhaustion of `latticeGraph 1 : SimpleGraph (Fin 1 → ℤ)`.
Provides the first concrete ℤ^d Ising Prop 4.6.1 convergence at general
ferromagnetic parameters (beyond the J = 0 / β = 0 trivial slices).

## Main definitions

* `linearBox (n : ℕ) : Finset (Fin 1 → ℤ)` — a 1D-line block of `n`
  points along coordinate 0. Cardinality is `n`.

## Main results

* `linearBox_card`, `linearBox_card_add` — cardinality is linear.
* `linearBox_disjoint_shift`, `linearBox_union_shift` — the union
  decomposition `linearBox (m + n) = linearBox m ∪ (shift_m +ᵥ linearBox n)`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
-/

namespace IsingModel

namespace Concrete

/-- **Linear brick** on `Fin 1 → ℤ`: the Finset of `n` points
`{fun _ => k | k ∈ Finset.Ico 0 n}`. Contiguous 1D line of length `n`
starting at the origin. -/
noncomputable def linearBox (n : ℕ) : Finset (Fin 1 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 1 => Finset.Ico (0 : ℤ) (n : ℤ))

/-- **Cardinality of `linearBox n`** equals `n`. -/
theorem linearBox_card (n : ℕ) : (linearBox n).card = n := by
  unfold linearBox
  rw [Fintype.card_piFinset]
  simp [Int.card_Ico]

/-- **Additive cardinality**: `|linearBox (m + n)| = |linearBox m| + |linearBox n|`.
Foundation for the `hcard_add` hypothesis of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive`. -/
theorem linearBox_card_add (m n : ℕ) :
    (linearBox (m + n)).card = (linearBox m).card + (linearBox n).card := by
  rw [linearBox_card, linearBox_card, linearBox_card]

/-- **Non-degeneracy of the base step**: `|linearBox 1| = 1 ≠ 0`. -/
theorem linearBox_one_card_ne_zero : (linearBox 1).card ≠ 0 := by
  rw [linearBox_card]; decide

/-- **Membership characterisation**: `v ∈ linearBox n ↔ 0 ≤ v 0 ∧ v 0 < n`. -/
theorem mem_linearBox {n : ℕ} {v : Fin 1 → ℤ} :
    v ∈ linearBox n ↔ 0 ≤ v 0 ∧ v 0 < (n : ℤ) := by
  unfold linearBox
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    have := h 0
    rw [Finset.mem_Ico] at this
    exact this
  · intro ⟨h1, h2⟩ i
    fin_cases i
    rw [Finset.mem_Ico]
    exact ⟨h1, h2⟩

/-- **Disjointness of shifted linear bricks**: `linearBox m` and the
`m`-shift of `linearBox n` (along direction 0) are disjoint. -/
theorem linearBox_disjoint_shift (m n : ℕ) :
    Disjoint (linearBox m)
      (Ambient.vaddFinset ((fun _ : Fin 1 => (m : ℤ)) : Fin 1 → ℤ) (linearBox n)) := by
  rw [Finset.disjoint_left]
  intro v hvm hvs
  rw [Ambient.mem_vaddFinset] at hvs
  obtain ⟨w, hw, hwv⟩ := hvs
  rw [mem_linearBox] at hvm
  rw [mem_linearBox] at hw
  -- hwv : (fun _ => (m : ℤ)) +ᵥ w = v, i.e., v 0 = m + w 0
  have hv0 : v 0 = (m : ℤ) + w 0 := by
    have : ((fun _ : Fin 1 => (m : ℤ)) +ᵥ w) 0 = v 0 := congrArg (· 0) hwv
    simp [vadd_eq_add] at this
    linarith
  omega

/-- **Union decomposition**:
`linearBox m ∪ (shift_m +ᵥ linearBox n) = linearBox (m + n)`. -/
theorem linearBox_union_shift (m n : ℕ) :
    linearBox m ∪
        Ambient.vaddFinset ((fun _ : Fin 1 => (m : ℤ)) : Fin 1 → ℤ) (linearBox n)
      = linearBox (m + n) := by
  ext v
  simp only [Finset.mem_union, Ambient.mem_vaddFinset, mem_linearBox]
  constructor
  · rintro (hleft | ⟨w, hw, hwv⟩)
    · refine ⟨hleft.1, ?_⟩
      have hmn : (m : ℤ) ≤ (m + n : ℕ) := by push_cast; linarith
      exact lt_of_lt_of_le hleft.2 hmn
    · have hv0 : v 0 = (m : ℤ) + w 0 := by
        have : ((fun _ : Fin 1 => (m : ℤ)) +ᵥ w) 0 = v 0 := congrArg (· 0) hwv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨?_, ?_⟩
      · rw [hv0]; linarith [hw.1]
      · rw [hv0]; push_cast; linarith [hw.2]
  · rintro ⟨h1, h2⟩
    by_cases hcase : v 0 < (m : ℤ)
    · left; exact ⟨h1, hcase⟩
    · right
      push Not at hcase
      refine ⟨fun _ : Fin 1 => v 0 - (m : ℤ), ⟨?_, ?_⟩, ?_⟩
      · linarith
      · push_cast at h2; linarith
      · funext i
        fin_cases i
        simp [vadd_eq_add]

end Concrete

end IsingModel
