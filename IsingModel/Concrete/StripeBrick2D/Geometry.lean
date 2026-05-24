import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum

/-!
# 2D rectangular stripe on `latticeGraph 2` (§4.6 Prop 4.6.1 concrete ℤ² instance)

Concrete application of
`Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive` (PR #638)
to the 2D stripe exhaustion
`stripeBrick2D (w : ℕ) (n : ℕ) : Finset (Fin 2 → ℤ) = [0, n) × [0, w)`
of `latticeGraph 2 : SimpleGraph (Fin 2 → ℤ)`. Strictly extends the 1D
linear-brick Fekete of PR #640 to a 2D instance with genuinely 2-dim
lattice couplings (adjacent rows interact).

## Main definitions

* `stripeBrick2D (w n : ℕ) : Finset (Fin 2 → ℤ)` — rectangular 2D stripe
  `[0, n) × [0, w)`, with `n` being the Fekete-growing length parameter
  and `w` the fixed width.

## Main results

* `stripeBrick2D_card`, `stripeBrick2D_card_add` — cardinality is linear
  in `n` (with coefficient `w`).
* `stripeBrick2D_disjoint_shift`, `stripeBrick2D_union_shift` — the union
  decomposition `stripeBrick2D w (m + n) = stripeBrick2D w m ∪
  (coord-0-shift_m +ᵥ stripeBrick2D w n)`.
* `log_partitionFunctionΛ_stripeBrick2D_super_additive` — super-additivity
  of `log Z` along the stripe sequence.
* `freeEnergy_stripeBrick2D_bddAbove` — uniform upper bound
  `log 2 + |β|·(2·|J| + |h|)` (d = 2 edge-count bound).
* `freeEnergy_stripeBrick2D_tendsto` — Fekete convergence of the
  free-energy-density sequence.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
-/

namespace IsingModel

namespace Concrete

/-- **2D rectangular stripe** on `Fin 2 → ℤ`: the Finset of
`n * w` points `{(k, ℓ) | 0 ≤ k < n, 0 ≤ ℓ < w}`. Rectangular
block of length `n` (coord 0) and fixed width `w` (coord 1). -/
noncomputable def stripeBrick2D (w n : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun i : Fin 2 =>
    Finset.Ico (0 : ℤ) (if i = 0 then (n : ℤ) else (w : ℤ)))

/-- **Cardinality of `stripeBrick2D w n`** equals `n * w`. -/
theorem stripeBrick2D_card (w n : ℕ) : (stripeBrick2D w n).card = n * w := by
  unfold stripeBrick2D
  rw [Fintype.card_piFinset]
  -- `∏ i : Fin 2, (Finset.Ico 0 (if i = 0 then n else w)).card`
  -- `= (Ico 0 n).card * (Ico 0 w).card = n * w`
  simp [Fin.prod_univ_succ, Int.card_Ico]

/-- **Additive cardinality in the length parameter**:
`|stripeBrick2D w (m + n)| = |stripeBrick2D w m| + |stripeBrick2D w n|`.
Foundation for the `hcard_add` hypothesis of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive`. -/
theorem stripeBrick2D_card_add (w m n : ℕ) :
    (stripeBrick2D w (m + n)).card
      = (stripeBrick2D w m).card + (stripeBrick2D w n).card := by
  rw [stripeBrick2D_card, stripeBrick2D_card, stripeBrick2D_card]
  ring

/-- **Non-degeneracy of the base step** for fixed width `w ≠ 0`:
`|stripeBrick2D w 1| = w ≠ 0`. -/
theorem stripeBrick2D_one_card_ne_zero {w : ℕ} (hw : w ≠ 0) :
    (stripeBrick2D w 1).card ≠ 0 := by
  rw [stripeBrick2D_card]; simpa using hw

/-- **Membership characterisation**: `v ∈ stripeBrick2D w n ↔
0 ≤ v 0 ∧ v 0 < n ∧ 0 ≤ v 1 ∧ v 1 < w`. -/
theorem mem_stripeBrick2D {w n : ℕ} {v : Fin 2 → ℤ} :
    v ∈ stripeBrick2D w n
      ↔ 0 ≤ v 0 ∧ v 0 < (n : ℤ) ∧ 0 ≤ v 1 ∧ v 1 < (w : ℤ) := by
  unfold stripeBrick2D
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Finset.mem_Ico] at h0 h1
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  · rintro ⟨h00, h01, h10, h11⟩ i
    fin_cases i
    · simp only [Fin.isValue, Finset.mem_Ico]; exact ⟨h00, h01⟩
    · simp only [Fin.isValue, Finset.mem_Ico]
      exact ⟨h10, h11⟩

/-- **Disjointness of shifted stripes**: `stripeBrick2D w m` and the
`m`-shift of `stripeBrick2D w n` along coord 0 are disjoint. -/
theorem stripeBrick2D_disjoint_shift (w m n : ℕ) :
    Disjoint (stripeBrick2D w m)
      (Ambient.vaddFinset
        ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) : Fin 2 → ℤ)
        (stripeBrick2D w n)) := by
  rw [Finset.disjoint_left]
  intro v hvm hvs
  rw [Ambient.mem_vaddFinset] at hvs
  obtain ⟨u, hu, huv⟩ := hvs
  rw [mem_stripeBrick2D] at hvm hu
  -- `huv : (shift +ᵥ u) = v`, so `v 0 = m + u 0`.
  have hv0 : v 0 = (m : ℤ) + u 0 := by
    have : ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) +ᵥ u) 0 = v 0 :=
      congrArg (· 0) huv
    simp [vadd_eq_add] at this
    linarith
  -- `hvm.2 : v 0 < m` but `hv0 : v 0 = m + u 0 ≥ m` (since `hu.1 : 0 ≤ u 0`).
  omega

/-- **Union decomposition**:
`stripeBrick2D w m ∪ (coord-0-shift_m +ᵥ stripeBrick2D w n)
  = stripeBrick2D w (m + n)`. -/
theorem stripeBrick2D_union_shift (w m n : ℕ) :
    stripeBrick2D w m ∪
        Ambient.vaddFinset
          ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) : Fin 2 → ℤ)
          (stripeBrick2D w n)
      = stripeBrick2D w (m + n) := by
  ext v
  simp only [Finset.mem_union, Ambient.mem_vaddFinset, mem_stripeBrick2D]
  constructor
  · rintro (⟨h00, h01, h10, h11⟩ | ⟨u, ⟨hu00, hu01, hu10, hu11⟩, huv⟩)
    · refine ⟨h00, ?_, h10, h11⟩
      have hmn : (m : ℤ) ≤ (m + n : ℕ) := by push_cast; linarith
      exact lt_of_lt_of_le h01 hmn
    · -- `huv : shift +ᵥ u = v` so `v 0 = m + u 0`, `v 1 = u 1`.
      have hv0 : v 0 = (m : ℤ) + u 0 := by
        have : ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) +ᵥ u) 0
            = v 0 := congrArg (· 0) huv
        simp [vadd_eq_add] at this
        linarith
      have hv1 : v 1 = u 1 := by
        have : ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) +ᵥ u) 1
            = v 1 := congrArg (· 1) huv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hv0]; linarith
      · rw [hv0]; push_cast; linarith
      · rw [hv1]; exact hu10
      · rw [hv1]; exact hu11
  · rintro ⟨h00, h01, h10, h11⟩
    by_cases hcase : v 0 < (m : ℤ)
    · left; exact ⟨h00, hcase, h10, h11⟩
    · right
      push Not at hcase
      refine ⟨fun i : Fin 2 => if i = 0 then v 0 - (m : ℤ) else v 1,
        ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Fin.isValue, ↓reduceIte]; linarith
      · simp only [Fin.isValue, ↓reduceIte]; push_cast at h01; linarith
      · simp only [Fin.isValue, one_ne_zero, ↓reduceIte]; exact h10
      · simp only [Fin.isValue, one_ne_zero, ↓reduceIte]; exact h11
      · funext i
        fin_cases i
        · -- Coord 0: `m + (v 0 - m) = v 0`.
          change ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) +ᵥ
              (fun j : Fin 2 => if j = 0 then v 0 - (m : ℤ) else v 1)) 0 = v 0
          simp only [Fin.isValue, ↓reduceIte, vadd_eq_add, Pi.add_apply]
          linarith
        · -- Coord 1: `0 + v 1 = v 1`.
          change ((fun i : Fin 2 => if i = 0 then (m : ℤ) else 0) +ᵥ
              (fun j : Fin 2 => if j = 0 then v 0 - (m : ℤ) else v 1)) 1 = v 1
          simp only [Fin.isValue, one_ne_zero, ↓reduceIte, vadd_eq_add,
            Pi.add_apply, zero_add]


end Concrete

end IsingModel
