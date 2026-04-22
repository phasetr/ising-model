import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LinearBrick
import IsingModel.Concrete.StripeBrick2D

/-!
# General `d+1`-dim slab on `latticeGraph (d+1)` (§4.6 Prop 4.6.1 concrete ℤ^(d+1))

General-dimension concrete application of
`Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive` (PR #638)
to the `d+1`-dimensional slab
`slabBrick widths n = [0, n) × ∏_{j : Fin d} [0, widths j) : Finset (Fin (d+1) → ℤ)`
of `latticeGraph (d + 1) : SimpleGraph (Fin (d+1) → ℤ)`. Subsumes the 1D
linear brick (PR #640, `d = 0`) and 2D rectangular stripe (PR #641,
`d = 1`, `widths = fun _ => w`) via the same Fekete scaffolding.

## Main definitions

* `slabBrick (widths : Fin d → ℕ) (n : ℕ) : Finset (Fin (d + 1) → ℤ)` —
  `d+1`-dim slab `[0, n) × ∏ [0, widths j)`, with coord 0 as the
  growing Fekete direction and coords `1..d` as the fixed cross-section.

## Main results

* `slabBrick_card`, `slabBrick_card_add` — cardinality is
  `n · ∏ widths j`, linear in `n`.
* `slabBrick_disjoint_shift`, `slabBrick_union_shift` — the union
  decomposition `slabBrick widths (m + n) = slabBrick widths m ∪
  (coord-0-shift_m +ᵥ slabBrick widths n)`.
* `log_partitionFunctionΛ_slabBrick_super_additive` — super-additivity
  of `log Z` along the slab sequence.
* `freeEnergy_slabBrick_bddAbove` — uniform upper bound
  `log 2 + |β|·((d+1)·|J| + |h|)` (from `|E| ≤ (d+1)·|V|`).
* `freeEnergy_slabBrick_tendsto` — Fekete convergence.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
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
private noncomputable def shiftCoord0 (m : ℕ) : Fin (d + 1) → ℤ :=
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

/-! ## Super-additivity, `BddAbove`, and Fekete convergence on the slab

With the combinatorial foundation above, apply the generic-Finset Fekete
theorem `Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) to conclude concrete Prop 4.6.1 convergence on the `d+1`-dim
slab (for any fixed positive widths). -/

/-- **Super-additivity of `log Z` on the slab** (ferromagnetic): for
fixed `widths` and every `m n : ℕ`,
`log Z_{slab widths m} + log Z_{slab widths n} ≤ log Z_{slab widths (m+n)}`.

Parallel to PR #640/#641: combines `log_partitionFunctionΛ_disjUnion_super_additive`
on `(slabBrick widths m, m-shift slabBrick widths n)` with translation
invariance (`partitionFunctionΛ_vaddFinset_eq`) and subsingleton transport
along `slabBrick_union_shift` (`partitionFunctionΛ_congr_finset`). -/
theorem log_partitionFunctionΛ_slabBrick_super_additive
    (widths : Fin d → ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (m n : ℕ) :
    Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1)) (slabBrick widths m) p)
        + Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1)) (slabBrick widths n) p)
      ≤ Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph (d + 1))
                (slabBrick widths (m + n)) p) := by
  have hTI : Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
      (Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n)) p
        = Ambient.partitionFunctionΛ (IsingModel.latticeGraph (d + 1))
              (slabBrick widths n) p :=
    Ambient.partitionFunctionΛ_vaddFinset_eq
      (IsingModel.latticeGraph (d + 1))
      (shiftCoord0 (d := d) m) (slabBrick widths n) p
  have hunion := slabBrick_union_shift widths m n
  have hdisj := slabBrick_disjoint_shift widths m n
  have hsup := Ambient.log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph (d + 1)) (Λ₁ := slabBrick widths m)
    (Λ₂ := Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n))
    hdisj p hf
  have hlog_shift : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1))
        (Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1)) (slabBrick widths n) p) :=
    congrArg Real.log hTI
  have hlog_union : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1))
        (slabBrick widths m ∪
          Ambient.vaddFinset (shiftCoord0 (d := d) m) (slabBrick widths n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph (d + 1)) (slabBrick widths (m + n)) p) :=
    congrArg Real.log (Ambient.partitionFunctionΛ_congr_finset
      (IsingModel.latticeGraph (d + 1)) hunion p)
  linarith [hsup, hlog_shift, hlog_union]

/-- **Per-stage uniform free-energy upper bound** on the `d+1`-dim slab
(ferromagnetic): for every `widths` and every `n : ℕ`,
`freeEnergy (inducedGraph (latticeGraph (d+1)) (slabBrick widths n)) p ≤
 log 2 + |β|·((d+1)·|J| + |h|)`.

Via `freeEnergy_upper_bound` + `inducedLatticeGraph_card_edgeFinset_le`
at `d' = d + 1` (`|E| ≤ (d+1)·|V|`). -/
theorem slabBrick_freeEnergy_le (widths : Fin d → ℕ) (n : ℕ)
    (p : IsingParams ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) p
      ≤ Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|) := by
  by_cases hn : (slabBrick widths n).card = 0
  · have hcard : Fintype.card (↑(slabBrick widths n) : Type _) = 0 := by
      rw [Fintype.card_coe]; exact hn
    have hfe : IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) p = 0 := by
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
  · have hcardpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
      rw [Fintype.card_coe]; exact Nat.pos_of_ne_zero hn
    have hub := IsingModel.freeEnergy_upper_bound
      (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
        (slabBrick widths n)) p hcardpos
    have hE := Ambient.inducedLatticeGraph_card_edgeFinset_le
      (d + 1) (slabBrick widths n)
    have hN_pos :
        (0 : ℝ) < (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ) := by
      exact_mod_cast hcardpos
    have hJabs_nn : (0 : ℝ) ≤ |p.J| := abs_nonneg _
    have hbeta_nn : (0 : ℝ) ≤ |p.β| := abs_nonneg _
    have hd_nn : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by push_cast; linarith
    -- Bound the numerator: `|J|·E + |h|·N ≤ ((d+1)|J| + |h|)·N` via `E ≤ (d+1)N`.
    have hJE : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)).edgeFinset.card : ℝ)
        ≤ |p.J| *
            (((d + 1 : ℕ) : ℝ) *
             (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ)) :=
      mul_le_mul_of_nonneg_left hE hJabs_nn
    have hnum : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)).edgeFinset.card : ℝ)
        + |p.h| * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ)
        ≤ (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
            * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ) := by
      nlinarith [hJE]
    have hfrac : |p.β| *
        (|p.J| *
          ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (slabBrick widths n)).edgeFinset.card : ℝ)
          + |p.h| * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ))
        / (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ)
          ≤ |p.β| * (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|) := by
      rw [div_le_iff₀ hN_pos]
      calc |p.β| *
            (|p.J| *
              ((Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
                (slabBrick widths n)).edgeFinset.card : ℝ)
              + |p.h| * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ))
          ≤ |p.β| *
              ((((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
                * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ)) :=
            mul_le_mul_of_nonneg_left hnum hbeta_nn
        _ = |p.β| * (((d + 1 : ℕ) : ℝ) * |p.J| + |p.h|)
              * (Fintype.card (↑(slabBrick widths n) : Type _) : ℝ) := by ring
    have hcast : ((d + 1 : ℕ) : ℝ) = ((d : ℝ) + 1) := by push_cast; ring
    rw [hcast] at hfrac
    linarith [hub, hfrac]

/-- **`BddAbove` of `freeEnergy` on the slab** (ferromagnetic):
for fixed `widths`, the free-energy-density sequence
`n ↦ freeEnergy_{slabBrick widths n}` is bounded above by
`log 2 + |β|·((d+1)·|J| + |h|)`, independent of `n`.

Wrapper around `slabBrick_freeEnergy_le`. -/
theorem freeEnergy_slabBrick_bddAbove (widths : Fin d → ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) p)) := by
  refine ⟨Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact slabBrick_freeEnergy_le widths n p

/-- **Concrete ℤ^(d+1) Ising free-energy-density Fekete convergence on
a fixed-width slab** (GJ §4.6 Prop 4.6.1 at general ferromagnetic
parameters, fixed positive `widths`): for any ferromagnetic `p` and
`widths : Fin d → ℕ` with `∀ j, widths j ≠ 0`, the sequence
`n ↦ freeEnergy (inducedGraph (latticeGraph (d+1)) (slabBrick widths n)) p`
converges.

Apply `Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) with the combinatorial inputs
`slabBrick_card_add`, `log_partitionFunctionΛ_slabBrick_super_additive`,
`freeEnergy_slabBrick_bddAbove`, and `slabBrick_one_card_ne_zero`. -/
theorem freeEnergy_slabBrick_tendsto
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) p)
      Filter.atTop (nhds L) :=
  Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive
    (IsingModel.latticeGraph (d + 1)) (slabBrick widths) p
    (slabBrick_card_add widths)
    (log_partitionFunctionΛ_slabBrick_super_additive widths p hf)
    (freeEnergy_slabBrick_bddAbove widths p)
    (slabBrick_one_card_ne_zero hw)

/-! ## Low-dimensional equivalences with `linearBox` and `stripeBrick2D`

These Finset equalities let callers transport results between the
low-dimensional concrete references and the general slab formulation. -/

/-- **1D equivalence**: the `d = 0` slab specialization (empty widths
via `Fin.elim0`) is literally the 1D linear brick `linearBox n`. -/
theorem linearBox_eq_slabBrick_elim0 (n : ℕ) :
    linearBox n = slabBrick Fin.elim0 n := by
  unfold linearBox slabBrick
  congr 1
  funext i
  -- `Fin.cases (n : ℤ) (fun _ : Fin 0 => ...) i = (n : ℤ)` for `i : Fin 1`.
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

/-- **2D equivalence**: the `d = 1` slab specialization (single width
`widths = fun _ : Fin 1 => w`) is literally the 2D stripe
`stripeBrick2D w n`. -/
theorem stripeBrick2D_eq_slabBrick (w n : ℕ) :
    stripeBrick2D w n = slabBrick (fun _ : Fin 1 => w) n := by
  unfold stripeBrick2D slabBrick
  congr 1
  funext i
  -- Both RHS args are `Finset.Ico 0 _`; show the upper bound matches.
  congr 1
  -- Goal: `(if i = 0 then (n : ℤ) else (w : ℤ)) = Fin.cases (n : ℤ) (fun _ => (w : ℤ)) i`
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

/-! ## Sandwich bounds for the slab (ferromagnetic)

Pair the upper bound `slabBrick_freeEnergy_le` (PR #642) with the
underlying lower bound `log 2 ≤ freeEnergy` (from
`freeEnergy_ge_log_two_of_ferromagnetic`) for the nonempty stages. -/

/-- **Lower bound** on the slab (ferromagnetic, nonempty slab):
`log 2 ≤ freeEnergy (inducedGraph (latticeGraph (d+1)) (slabBrick widths n)) p`.

Derived from the base-layer `freeEnergy_ge_log_two_of_ferromagnetic`
via the `Finset.Nonempty` coe-cardinality bridge. -/
theorem slabBrick_freeEnergy_ge_log_two {widths : Fin d → ℕ} {n : ℕ}
    (hne : (slabBrick widths n).Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (slabBrick widths n))
          (⟨J, h, β⟩ : IsingParams ℝ) := by
  have hpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Sandwich bound** on the slab (ferromagnetic, nonempty slab):
`log 2 ≤ freeEnergy ≤ log 2 + |β|·((d+1)·|J| + |h|)`.

Combines `slabBrick_freeEnergy_ge_log_two` and `slabBrick_freeEnergy_le`.
Concrete slab-version of the cubic sandwich
`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_bounds` (PR #247). -/
theorem slabBrick_freeEnergy_sandwich {widths : Fin d → ℕ} {n : ℕ}
    (hne : (slabBrick widths n).Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (slabBrick widths n))
          (⟨J, h, β⟩ : IsingParams ℝ)
    ∧ IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
            (slabBrick widths n))
          (⟨J, h, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨slabBrick_freeEnergy_ge_log_two hne hJ hh hβ,
   slabBrick_freeEnergy_le widths n ⟨J, h, β⟩⟩

/-! ## Named infinite-volume limit -/

/-- **Infinite-volume free-energy density along the slab sequence**.
The `Classical.choose` witness of `freeEnergy_slabBrick_tendsto`,
pinning down the limit value of the Fekete-convergent sequence for
ferromagnetic `p` and all-positive `widths`. -/
noncomputable def freeEnergyInfinite_slabBrick
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) : ℝ :=
  Classical.choose (freeEnergy_slabBrick_tendsto hw p hf)

/-- **Convergence to the named limit**: the slab free-energy-density
sequence converges to `freeEnergyInfinite_slabBrick hw p hf`. -/
theorem freeEnergy_slabBrick_tendsto_freeEnergyInfinite
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_slabBrick hw p hf)) :=
  Classical.choose_spec (freeEnergy_slabBrick_tendsto hw p hf)

/-- **`slabBrick widths n` is nonempty** when all widths are nonzero
and `n ≥ 1`. Derived from the cardinality identity
`|slabBrick widths n| = n · ∏ widths j`. -/
theorem slabBrick_nonempty {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (slabBrick widths n).Nonempty := by
  rw [← Finset.card_pos, slabBrick_card]
  have hprod : 0 < ∏ j : Fin d, widths j :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hw j))
  exact Nat.mul_pos hn hprod

/-- **J=0 closed form for the infinite-volume free-energy density**
on the slab: `freeEnergyInfinite_slabBrick hw ⟨0, h, β⟩ hf = log(2·cosh(β·h))`.

Per-stage value is constant `log(2·cosh(β·h))` for nonempty slabs
(via `IsingModel.freeEnergy_J_zero`); the sequence is eventually
constant along `atTop`, so `tendsto_nhds_unique` pins the named
infinite-volume limit. -/
theorem freeEnergyInfinite_slabBrick_J_zero {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_slabBrick hw
        (⟨0, h, β⟩ : IsingParams ℝ) ⟨le_refl 0, hh, hβ⟩
      = Real.log (2 * Real.cosh (β * h)) := by
  have hconst : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n)) (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hne : (slabBrick widths n).Nonempty := slabBrick_nonempty hw hn
    have hpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
    exact (IsingModel.freeEnergy_J_zero _ h β hpos).symm
  exact tendsto_nhds_unique
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ _) hconst

/-- **Infinite-volume lower bound** on the slab. -/
theorem freeEnergyInfinite_slabBrick_ge_log_two {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite_slabBrick hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (slabBrick widths n).Nonempty := slabBrick_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Infinite-volume upper bound** on the slab. -/
theorem freeEnergyInfinite_slabBrick_le {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_slabBrick hw p hf
      ≤ Real.log 2 + |p.β| * ((d + 1) * |p.J| + |p.h|) := by
  refine le_of_tendsto
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards with n
  exact slabBrick_freeEnergy_le widths n p

/-- **Infinite-volume sandwich** on the slab (ferromagnetic). -/
theorem freeEnergyInfinite_slabBrick_sandwich {widths : Fin d → ℕ}
    (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
        ≤ freeEnergyInfinite_slabBrick hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_slabBrick hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨freeEnergyInfinite_slabBrick_ge_log_two hw hJ hh hβ,
   freeEnergyInfinite_slabBrick_le hw _ ⟨hJ, hh, hβ⟩⟩

/-! ## Low-dimensional equivalences for the named infinite-volume limits

Transport the Finset equalities `linearBox_eq_slabBrick_elim0` and
`stripeBrick2D_eq_slabBrick` through the Fekete limit: since the
underlying convergent sequences agree pointwise, their named limits
coincide. -/

/-- **1D limit equivalence**: the 1D linearBox named limit equals the
`d = 0` slab specialization (empty widths via `Fin.elim0`). -/
theorem freeEnergyInfinite_linearBox_eq_slabBrick_elim0
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_linearBox p hf
      = @freeEnergyInfinite_slabBrick 0 (Fin.elim0 : Fin 0 → ℕ)
          (fun j => j.elim0) p hf := by
  have hpt : ∀ n : ℕ,
      IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p
      = IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (0 + 1))
          (slabBrick (d := 0) Fin.elim0 n)) p := by
    intro n; rw [linearBox_eq_slabBrick_elim0]
  have htendsto : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (0 + 1))
          (slabBrick (d := 0) Fin.elim0 n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) := by
    refine (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf).congr ?_
    intro n; exact hpt n
  exact (tendsto_nhds_unique htendsto
    (@freeEnergy_slabBrick_tendsto_freeEnergyInfinite 0 Fin.elim0
      (fun j => j.elim0) p hf)).symm

/-- **2D limit equivalence**: the 2D stripe named limit equals the
`d = 1` slab specialization with constant width. -/
theorem freeEnergyInfinite_stripeBrick2D_eq_slabBrick
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_stripeBrick2D hw p hf
      = @freeEnergyInfinite_slabBrick 1 (fun _ : Fin 1 => w)
          (fun _ => hw) p hf := by
  have hpt : ∀ n : ℕ,
      IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)) p
      = IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (1 + 1))
          (slabBrick (d := 1) (fun _ : Fin 1 => w) n)) p := by
    intro n; rw [stripeBrick2D_eq_slabBrick]
  have htendsto : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (1 + 1))
          (slabBrick (d := 1) (fun _ : Fin 1 => w) n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_stripeBrick2D hw p hf)) := by
    refine (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw p hf).congr ?_
    intro n; exact hpt n
  exact (tendsto_nhds_unique htendsto
    (@freeEnergy_slabBrick_tendsto_freeEnergyInfinite 1 (fun _ : Fin 1 => w)
      (fun _ => hw) p hf)).symm

/-! ## Translation invariance of the named infinite-volume limit

Any coord-shift of the slab sequence converges to the same
`freeEnergyInfinite_slabBrick` value, via translation invariance of
`freeEnergyΛ` on the (translation-invariant) `latticeGraph (d+1)`. -/

/-- **Translation-invariance of the Fekete limit** on the slab: for
any `t : Fin (d+1) → ℤ`, the shifted sequence
`n ↦ freeEnergy (inducedGraph (latticeGraph (d+1)) (t +ᵥ slabBrick widths n))`
converges to the same `freeEnergyInfinite_slabBrick hw p hf`. -/
theorem freeEnergyInfinite_slabBrick_tendsto_shift
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Fin (d + 1) → ℤ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (Ambient.vaddFinset t (slabBrick widths n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_slabBrick hw p hf)) := by
  refine (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw p hf).congr ?_
  intro n
  -- `freeEnergy (inducedGraph G Λ) p = freeEnergy (inducedGraph G (t +ᵥ Λ)) p`
  -- via `Ambient.freeEnergyΛ_vaddFinset_eq` (translation invariance of Λ-form).
  exact (Ambient.freeEnergyΛ_vaddFinset_eq
    (IsingModel.latticeGraph (d + 1)) t (slabBrick widths n) p).symm

/-- **Nonnegativity** of `freeEnergyInfinite_slabBrick` under
ferromagnetic parameters. -/
theorem freeEnergyInfinite_slabBrick_nonneg
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite_slabBrick hw p hf := by
  refine ge_of_tendsto
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (slabBrick widths n).Nonempty := slabBrick_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_nonneg_of_ferromagnetic _ p hf hpos

/-- **Tighter lower bound** `log(2·cosh(β·h)) ≤ freeEnergyInfinite_slabBrick`. -/
theorem freeEnergyInfinite_slabBrick_ge_log_two_cosh
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyInfinite_slabBrick hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ⟩) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (slabBrick widths n).Nonempty := slabBrick_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(slabBrick widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hpos

/-- **Cosh-form sandwich** on the slab. -/
theorem freeEnergyInfinite_slabBrick_sandwich_cosh
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
        ≤ freeEnergyInfinite_slabBrick hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_slabBrick hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨freeEnergyInfinite_slabBrick_ge_log_two_cosh hw hJ hh hβ,
   freeEnergyInfinite_slabBrick_le hw _ ⟨hJ, hh, hβ⟩⟩

/-- **β-monotonicity** of `freeEnergyInfinite_slabBrick`. -/
theorem freeEnergyInfinite_slabBrick_monotone_beta
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβle : β₁ ≤ β₂) :
    freeEnergyInfinite_slabBrick hw
        (⟨J, h, β₁⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₁⟩
      ≤ freeEnergyInfinite_slabBrick hw
        (⟨J, h, β₂⟩ : IsingParams ℝ) ⟨hJ, hh, hβ₂⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₁⟩)
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ₂⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_beta _ J hJ h hh hβ₁ hβ₂ hβle

/-- **h-monotonicity** of `freeEnergyInfinite_slabBrick`. -/
theorem freeEnergyInfinite_slabBrick_monotone_h
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hhle : h₁ ≤ h₂) :
    freeEnergyInfinite_slabBrick hw
        (⟨J, h₁, β⟩ : IsingParams ℝ) ⟨hJ, hh₁, hβ⟩
      ≤ freeEnergyInfinite_slabBrick hw
        (⟨J, h₂, β⟩ : IsingParams ℝ) ⟨hJ, hh₂, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₁, hβ⟩)
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh₂, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_h _ J β hJ hβ hh₁ hh₂ hhle

/-- **J-monotonicity** of `freeEnergyInfinite_slabBrick`. -/
theorem freeEnergyInfinite_slabBrick_monotone_J
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) (hJle : J₁ ≤ J₂) :
    freeEnergyInfinite_slabBrick hw
        (⟨J₁, h, β⟩ : IsingParams ℝ) ⟨hJ₁, hh, hβ⟩
      ≤ freeEnergyInfinite_slabBrick hw
        (⟨J₂, h, β⟩ : IsingParams ℝ) ⟨hJ₂, hh, hβ⟩ := by
  refine le_of_tendsto_of_tendsto'
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ₁, hh, hβ⟩)
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw _ ⟨hJ₂, hh, hβ⟩) ?_
  intro n
  exact IsingModel.freeEnergy_monotone_J _ h β hh hβ hJ₁ hJ₂ hJle

/-- **Fekete convergence for any real h** on the slab. -/
theorem freeEnergy_slabBrick_tendsto_of_abs_h
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (h : ℝ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths n))
        (⟨J, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite_slabBrick hw
        (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩)) := by
  refine (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw
    (⟨J, |h|, β⟩ : IsingParams ℝ) ⟨hJ, abs_nonneg h, hβ⟩).congr ?_
  intro n
  exact (IsingModel.freeEnergy_eq_abs_h _ J h β).symm

end Concrete

end IsingModel
