import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum

/-!
# Two-sided centered slab on `latticeGraph (d+1)` (§4.6 Prop 4.6.1 strip convergence)

Concrete application of
`Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive` (PR #638)
to a two-sided (origin-centered) slab sequence on
`latticeGraph (d + 1) : SimpleGraph (Fin (d+1) → ℤ)`:

`centeredSlab widths n = [-n, n) × ∏ [0, widths j) : Finset (Fin (d+1) → ℤ)`

with coord 0 two-sided `[-n, n)` (cardinality `2n`, linear in `n`) and
coords `1..d` fixed `[0, widths j)`. Complements the single-sided
general slab of PR #642 by using a symmetric `[-n, n)` range on coord 0.

*Not* a van Hove / Følner sequence in the ambient `ℤ^(d+1)` lattice:
with fixed transverse widths, the side-boundary in the fixed
directions is `Θ(n)`, of the same order as the volume `Θ(n)`. The
Fekete convergence obtained here is for the one-parameter family of
increasing strips/slabs, not for full `ℤ^(d+1)` van Hove exhaustion.

The key difference from the single-sided slab is the Fekete
decomposition: `centeredSlab (m+n) = shift_(-n) (centeredSlab m) ∪
shift_m (centeredSlab n)` involves **two** shifts (one negative, one
positive), yielding the open interval identity
`[-m-n, m+n) = [-m-n, m-n) ∪ [m-n, m+n)`.

## Main definitions

* `centeredSlab (widths : Fin d → ℕ) (n : ℕ) : Finset (Fin (d+1) → ℤ)`
  — the two-sided `d+1`-dim slab centered at the origin on coord 0.

## Main results

* `centeredSlab_card`, `centeredSlab_card_add`, `mem_centeredSlab`,
  `centeredSlab_one_card_ne_zero`, `centeredSlab_disjoint_double_shift`,
  `centeredSlab_union_double_shift`.
* `log_partitionFunctionΛ_centeredSlab_super_additive`,
  `centeredSlab_freeEnergy_le` / `freeEnergy_centeredSlab_bddAbove`,
  `freeEnergy_centeredSlab_tendsto`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
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
private noncomputable def shiftCoord0Int (k : ℤ) : Fin (d + 1) → ℤ :=
  Fin.cases k (fun _ : Fin d => (0 : ℤ))

@[simp]
private theorem shiftCoord0Int_zero (k : ℤ) :
    (shiftCoord0Int (d := d) k) 0 = k := by
  unfold shiftCoord0Int; rfl

@[simp]
private theorem shiftCoord0Int_succ (k : ℤ) (j : Fin d) :
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

/-! ## Super-additivity, `BddAbove`, and Fekete convergence on the centered slab -/

/-- **Super-additivity of `log Z` on the centered slab** (ferromagnetic):
for fixed `widths` and every `m n : ℕ`,
`log Z_{centered m} + log Z_{centered n} ≤ log Z_{centered (m+n)}`.

Parallel structure to PR #642's single-sided slab: disjoint-union
super-additivity + translation invariance applied to **both** shifted
halves + subsingleton transport along `centeredSlab_union_double_shift`. -/
theorem log_partitionFunctionΛ_centeredSlab_super_additive
    (widths : Fin d → ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (m n : ℕ) :
    Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1)) (centeredSlab widths m) p)
        + Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1)) (centeredSlab widths n) p)
      ≤ Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1))
                (centeredSlab widths (m + n)) p) := by
  have hTI_left :
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
          (centeredSlab widths m)) p
        = Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
              (centeredSlab widths m) p :=
    Ambient.partitionFunctionΛ_vaddFinset_eq
      (IsingModel.latticeGraph (d + 1))
      (shiftCoord0Int (d := d) (-(n : ℤ))) (centeredSlab widths m) p
  have hTI_right :
      Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
          (centeredSlab widths n)) p
        = Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
              (centeredSlab widths n) p :=
    Ambient.partitionFunctionΛ_vaddFinset_eq
      (IsingModel.latticeGraph (d + 1))
      (shiftCoord0Int (d := d) (m : ℤ)) (centeredSlab widths n) p
  have hunion := centeredSlab_union_double_shift widths m n
  have hdisj := centeredSlab_disjoint_double_shift widths m n
  have hsup := Ambient.log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph (d + 1))
    (Λ₁ := Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
            (centeredSlab widths m))
    (Λ₂ := Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
            (centeredSlab widths n))
    hdisj p hf
  have hlog_left : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
          (centeredSlab widths m)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1)) (centeredSlab widths m) p) :=
    congrArg Real.log hTI_left
  have hlog_right : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
          (centeredSlab widths n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1)) (centeredSlab widths n) p) :=
    congrArg Real.log hTI_right
  have hlog_union : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
          (centeredSlab widths m)
          ∪ Ambient.vaddFinset (shiftCoord0Int (d := d) (m : ℤ))
              (centeredSlab widths n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1)) (centeredSlab widths (m + n)) p) :=
    congrArg Real.log (Ambient.partitionFunctionΛ_congr_finset
      (IsingModel.latticeGraph (d + 1)) hunion p)
  linarith [hsup, hlog_left, hlog_right, hlog_union]

/-- **Per-stage uniform free-energy upper bound** on the centered slab:
for every `widths` and every `n : ℕ`,
`freeEnergy ≤ log 2 + |β|·((d+1)·|J| + |h|)`. -/
theorem centeredSlab_freeEnergy_le (widths : Fin d → ℕ) (n : ℕ)
    (p : IsingParams ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p
      ≤ Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|) := by
  by_cases hn : (centeredSlab widths n).card = 0
  · have hcard : Fintype.card (↑(centeredSlab widths n) : Type _) = 0 := by
      rw [Fintype.card_coe]; exact hn
    have hfe : IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p = 0 := by
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]
    have hJ : (0 : ℝ) ≤ |p.J| := abs_nonneg _
    have hh : (0 : ℝ) ≤ |p.h| := abs_nonneg _
    have hβ : (0 : ℝ) ≤ |p.β| := abs_nonneg _
    have hd_nn : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : (0 : ℝ) ≤ |p.β| * ((d + 1 : ℕ) * |p.J| + |p.h|) := by
      have : (0 : ℝ) ≤ (d + 1 : ℕ) * |p.J| + |p.h| :=
        add_nonneg (mul_nonneg hd_nn hJ) hh
      exact mul_nonneg hβ this
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    push_cast at h1 ⊢
    linarith
  · have hcardpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
      rw [Fintype.card_coe]; exact Nat.pos_of_ne_zero hn
    have hub := IsingModel.freeEnergy_upper_bound
      (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
        (centeredSlab widths n)) p hcardpos
    have hE := Ambient.inducedLatticeGraph_card_edgeFinset_le
      (d + 1) (centeredSlab widths n)
    have hN_pos :
        (0 : ℝ) < (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ) := by
      exact_mod_cast hcardpos
    have hJabs_nn : (0 : ℝ) ≤ |p.J| := abs_nonneg _
    have hbeta_nn : (0 : ℝ) ≤ |p.β| := abs_nonneg _
    have hJE : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)).edgeFinset.card : ℝ)
        ≤ |p.J| *
            (((d + 1 : ℕ) : ℝ) *
             (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ)) :=
      mul_le_mul_of_nonneg_left hE hJabs_nn
    have hnum : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)).edgeFinset.card : ℝ)
        + |p.h| * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ)
        ≤ (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
            * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ) := by
      nlinarith [hJE]
    have hfrac : |p.β| *
        (|p.J| *
          ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (centeredSlab widths n)).edgeFinset.card : ℝ)
          + |p.h| * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ))
        / (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ)
          ≤ |p.β| * (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|) := by
      rw [div_le_iff₀ hN_pos]
      calc |p.β| *
            (|p.J| *
              ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
                (centeredSlab widths n)).edgeFinset.card : ℝ)
              + |p.h| * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ))
          ≤ |p.β| *
              ((((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
                * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ)) :=
            mul_le_mul_of_nonneg_left hnum hbeta_nn
        _ = |p.β| * (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
              * (Fintype.card (↑(centeredSlab widths n) : Type _) : ℝ) := by ring
    have hcast : ((d + 1 : ℕ) : ℝ) = ((d : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hfrac
    linarith [hub, hfrac]

/-- **`BddAbove` of `freeEnergy` on the centered slab**. -/
theorem freeEnergy_centeredSlab_bddAbove (widths : Fin d → ℕ)
    (p : IsingParams ℝ) :
    BddAbove (Set.range
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p)) := by
  refine ⟨Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact centeredSlab_freeEnergy_le widths n p

/-- **Two-sided centered-slab Fekete convergence** (GJ §4.6 Prop 4.6.1,
strip/slab form): for any ferromagnetic `p` and `widths : Fin d → ℕ`
with `∀ j, widths j ≠ 0`, the sequence along the two-sided centered
slab converges. (Not a full-lattice van Hove statement — see module
header.) -/
theorem freeEnergy_centeredSlab_tendsto
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p)
      Filter.atTop (nhds L) :=
  Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive
    (IsingModel.latticeGraph (d + 1)) (centeredSlab widths) p
    (centeredSlab_card_add widths)
    (log_partitionFunctionΛ_centeredSlab_super_additive widths p hf)
    (freeEnergy_centeredSlab_bddAbove widths p)
    (centeredSlab_one_card_ne_zero hw)

/-! ## Sandwich bounds for the centered slab (ferromagnetic) -/

/-- **Lower bound** on the centered slab (ferromagnetic, nonempty):
`log 2 ≤ freeEnergy (inducedGraph (latticeGraph (d+1)) (centeredSlab widths n)) p`. -/
theorem centeredSlab_freeEnergy_ge_log_two {widths : Fin d → ℕ} {n : ℕ}
    (hne : (centeredSlab widths n).Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (centeredSlab widths n))
          (⟨J, h, β⟩ : IsingParams ℝ) := by
  have hpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Sandwich bound** on the centered slab (ferromagnetic, nonempty):
`log 2 ≤ freeEnergy ≤ log 2 + |β|·((d+1)·|J| + |h|)`.

Combines `centeredSlab_freeEnergy_ge_log_two` and
`centeredSlab_freeEnergy_le`. -/
theorem centeredSlab_freeEnergy_sandwich {widths : Fin d → ℕ} {n : ℕ}
    (hne : (centeredSlab widths n).Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (centeredSlab widths n))
          (⟨J, h, β⟩ : IsingParams ℝ)
    ∧ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (centeredSlab widths n))
          (⟨J, h, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨centeredSlab_freeEnergy_ge_log_two hne hJ hh hβ,
   centeredSlab_freeEnergy_le widths n ⟨J, h, β⟩⟩

/-! ## Named infinite-volume limit -/

/-- **Infinite-volume free-energy density along the centered slab
sequence**. The `Classical.choose` witness of
`freeEnergy_centeredSlab_tendsto`, pinning down the limit value of
the Fekete-convergent sequence for ferromagnetic `p` and all-positive
`widths`. -/
noncomputable def freeEnergyInfinite_centeredSlab
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) : ℝ :=
  Classical.choose (freeEnergy_centeredSlab_tendsto hw p hf)

/-- **Convergence to the named limit**: the centered slab
free-energy-density sequence converges to
`freeEnergyInfinite_centeredSlab hw p hf`. -/
theorem freeEnergy_centeredSlab_tendsto_freeEnergyInfinite
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_centeredSlab hw p hf)) :=
  Classical.choose_spec (freeEnergy_centeredSlab_tendsto hw p hf)

/-- **`centeredSlab widths n` is nonempty** when all widths are nonzero
and `n ≥ 1`. Derived from `|centeredSlab widths n| = 2n · ∏ widths`. -/
theorem centeredSlab_nonempty {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (centeredSlab widths n).Nonempty := by
  rw [← Finset.card_pos, centeredSlab_card]
  have hprod : 0 < ∏ j : Fin d, widths j :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hw j))
  have h2n : 0 < 2 * n := by linarith
  exact Nat.mul_pos h2n hprod

/-- **J=0 closed form for the centered-slab infinite-volume
free-energy density**: `freeEnergyInfinite_centeredSlab hw ⟨0, h, β⟩ hf
= log(2·cosh(β·h))` under ferromagnetic `0 ≤ h, 0 < β`. Parallel to
`freeEnergyInfinite_slabBrick_J_zero`. -/
theorem freeEnergyInfinite_centeredSlab_J_zero {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_centeredSlab hw
        (⟨0, h, β⟩ : IsingParams ℝ) ⟨le_refl 0, hh, hβ⟩
      = Real.log (2 * Real.cosh (β * h)) := by
  have hconst : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hne : (centeredSlab widths n).Nonempty := centeredSlab_nonempty hw hn
    have hpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
    exact (IsingModel.freeEnergy_J_zero _ h β hpos).symm
  exact tendsto_nhds_unique
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ _) hconst

/-- **Infinite-volume lower bound** on the centered slab. -/
theorem freeEnergyInfinite_centeredSlab_ge_log_two {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite_centeredSlab hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (centeredSlab widths n).Nonempty := centeredSlab_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Infinite-volume upper bound** on the centered slab. -/
theorem freeEnergyInfinite_centeredSlab_le {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_centeredSlab hw p hf
      ≤ Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|) := by
  refine le_of_tendsto
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards with n
  exact centeredSlab_freeEnergy_le widths n p

/-- **Infinite-volume sandwich** on the centered slab (ferromagnetic). -/
theorem freeEnergyInfinite_centeredSlab_sandwich {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
        ≤ freeEnergyInfinite_centeredSlab hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_centeredSlab hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨freeEnergyInfinite_centeredSlab_ge_log_two hw hJ hh hβ,
   freeEnergyInfinite_centeredSlab_le hw _ ⟨hJ, hh, hβ⟩⟩

/-- **Translation-invariance of the Fekete limit** on the centered
slab: any coord-shift of the centered-slab sequence converges to the
same `freeEnergyInfinite_centeredSlab hw p hf`. -/
theorem freeEnergyInfinite_centeredSlab_tendsto_shift
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Fin (d + 1) → ℤ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (Ambient.vaddFinset t (centeredSlab widths n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_centeredSlab hw p hf)) := by
  refine (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw p hf).congr ?_
  intro n
  exact (Ambient.freeEnergyΛ_vaddFinset_eq
    (IsingModel.latticeGraph (d + 1)) t (centeredSlab widths n) p).symm

end Concrete

end IsingModel
