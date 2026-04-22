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

/-! ## Super-additivity, `BddAbove`, and Fekete convergence on the 2D stripe

With the combinatorial foundation above, apply the generic-Finset
Fekete theorem
`Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) to conclude concrete Prop 4.6.1 convergence on the 2D
stripe (for any fixed width `w`). -/

/-- **Super-additivity of `log Z` on the 2D stripe** (ferromagnetic):
for fixed width `w` and every `m n : ℕ`,
`log Z_{stripe w m} + log Z_{stripe w n} ≤ log Z_{stripe w (m + n)}`.

Parallel to PR #640's 1D `log_partitionFunctionΛ_linearBox_super_additive`:
combines `log_partitionFunctionΛ_disjUnion_super_additive` on the disjoint
pair (`stripeBrick2D w m`, `m`-shift of `stripeBrick2D w n`) with
translation invariance (`partitionFunctionΛ_vaddFinset_eq`) and
`partitionFunctionΛ_congr_finset` (for the subsingleton transport along
`stripeBrick2D_union_shift`). -/
theorem log_partitionFunctionΛ_stripeBrick2D_super_additive
    (w : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ) :
    Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 2) (stripeBrick2D w m) p)
        + Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 2) (stripeBrick2D w n) p)
      ≤ Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 2) (stripeBrick2D w (m + n)) p) := by
  set shift_m : Fin 2 → ℤ := fun i => if i = 0 then (m : ℤ) else 0 with hshift
  have hTI : Ambient.partitionFunctionΛ (IsingModel.latticeGraph 2)
      (Ambient.vaddFinset shift_m (stripeBrick2D w n)) p
        = Ambient.partitionFunctionΛ (IsingModel.latticeGraph 2)
              (stripeBrick2D w n) p :=
    Ambient.partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph 2)
      shift_m (stripeBrick2D w n) p
  have hunion := stripeBrick2D_union_shift w m n
  have hdisj := stripeBrick2D_disjoint_shift w m n
  have hsup := Ambient.log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph 2) (Λ₁ := stripeBrick2D w m)
    (Λ₂ := Ambient.vaddFinset shift_m (stripeBrick2D w n)) hdisj p hf
  have hlog_shift : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 2)
        (Ambient.vaddFinset shift_m (stripeBrick2D w n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 2) (stripeBrick2D w n) p) :=
    congrArg Real.log hTI
  have hlog_union : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 2)
        (stripeBrick2D w m ∪ Ambient.vaddFinset shift_m (stripeBrick2D w n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 2) (stripeBrick2D w (m + n)) p) :=
    congrArg Real.log (Ambient.partitionFunctionΛ_congr_finset
      (IsingModel.latticeGraph 2) hunion p)
  linarith [hsup, hlog_shift, hlog_union]

/-- **Per-stage uniform free-energy upper bound** on the 2D stripe
(ferromagnetic): for fixed width `w` and every `n : ℕ`,
`freeEnergy (inducedGraph (latticeGraph 2) (stripeBrick2D w n)) p ≤
 log 2 + |β|·(2·|J| + |h|)`.

Via `freeEnergy_upper_bound` applied per stage, combined with the
edge-count bound `Ambient.inducedLatticeGraph_card_edgeFinset_le` at
`d = 2` (= `|E| ≤ 2 · |Λ|`). -/
theorem stripeBrick2D_freeEnergy_le (w n : ℕ) (p : IsingParams ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2) (stripeBrick2D w n)) p
      ≤ Real.log 2 + |p.β| * (2 * |p.J| + |p.h|) := by
  by_cases hn : (stripeBrick2D w n).card = 0
  · -- Empty stripe: `freeEnergy = 0` by the `invert of zero` convention.
    have hcard : Fintype.card (↑(stripeBrick2D w n) : Type _) = 0 := by
      rw [Fintype.card_coe]; exact hn
    have hfe : IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2) (stripeBrick2D w n)) p
          = 0 := by
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]
    have h1 : (0 : ℝ) ≤ |p.β| * (2 * |p.J| + |p.h|) := by
      have hJ : (0 : ℝ) ≤ |p.J| := abs_nonneg _
      have hh : (0 : ℝ) ≤ |p.h| := abs_nonneg _
      have hβ : (0 : ℝ) ≤ |p.β| := abs_nonneg _
      have : (0 : ℝ) ≤ 2 * |p.J| + |p.h| := by linarith
      exact mul_nonneg hβ this
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hcardpos : 0 < Fintype.card (↑(stripeBrick2D w n) : Type _) := by
      rw [Fintype.card_coe]; exact Nat.pos_of_ne_zero hn
    have hub := IsingModel.freeEnergy_upper_bound
      (Ambient.inducedGraph (IsingModel.latticeGraph 2) (stripeBrick2D w n))
      p hcardpos
    have hE := Ambient.inducedLatticeGraph_card_edgeFinset_le 2 (stripeBrick2D w n)
    have hN_pos : (0 : ℝ) < (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ) := by
      exact_mod_cast hcardpos
    -- Bound the numerator: `|J|·E + |h|·N ≤ (2|J| + |h|)·N` via `E ≤ 2N`.
    have hJabs_nn : (0 : ℝ) ≤ |p.J| := abs_nonneg _
    have hbeta_nn : (0 : ℝ) ≤ |p.β| := abs_nonneg _
    have h2nn : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) := by push_cast; norm_num
    have hJE : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)).edgeFinset.card : ℝ)
        ≤ |p.J| *
            (((2 : ℕ) : ℝ) *
             (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ)) :=
      mul_le_mul_of_nonneg_left hE hJabs_nn
    have h2r : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_cast
    rw [h2r] at hJE
    have hnum : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)).edgeFinset.card : ℝ)
        + |p.h| * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ)
        ≤ (2 * |p.J| + |p.h|)
            * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ) := by
      nlinarith [hJE]
    have hfrac : |p.β| *
        (|p.J| *
          ((Ambient.inducedGraph (IsingModel.latticeGraph 2)
            (stripeBrick2D w n)).edgeFinset.card : ℝ)
          + |p.h| * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ))
        / (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ)
          ≤ |p.β| * (2 * |p.J| + |p.h|) := by
      rw [div_le_iff₀ hN_pos]
      calc |p.β| *
            (|p.J| *
              ((Ambient.inducedGraph (IsingModel.latticeGraph 2)
                (stripeBrick2D w n)).edgeFinset.card : ℝ)
              + |p.h| * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ))
          ≤ |p.β| *
              ((2 * |p.J| + |p.h|)
                * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ)) :=
            mul_le_mul_of_nonneg_left hnum hbeta_nn
        _ = |p.β| * (2 * |p.J| + |p.h|)
              * (Fintype.card (↑(stripeBrick2D w n) : Type _) : ℝ) := by ring
    linarith [hub, hfrac]

/-- **`BddAbove` of `freeEnergy` on the 2D stripe** (ferromagnetic):
for fixed `w`, the free-energy-density sequence `n ↦ freeEnergy_{stripe w n}`
is bounded above by `log 2 + |β|·(2·|J| + |h|)`, independent of `n`.

Wrapper around `stripeBrick2D_freeEnergy_le`. -/
theorem freeEnergy_stripeBrick2D_bddAbove (w : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)) p)) := by
  refine ⟨Real.log 2 + |p.β| * (2 * |p.J| + |p.h|), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact stripeBrick2D_freeEnergy_le w n p

/-- **Concrete ℤ² 2D Ising free-energy-density Fekete convergence on
a fixed-width stripe** (GJ §4.6 Prop 4.6.1 at general ferromagnetic
parameters, fixed width `w ≠ 0`): for any ferromagnetic `p` and
positive width `w`, the sequence
`n ↦ freeEnergy (inducedGraph (latticeGraph 2) (stripeBrick2D w n)) p`
converges.

Apply `Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) with the combinatorial inputs
`stripeBrick2D_card_add`, `log_partitionFunctionΛ_stripeBrick2D_super_additive`,
`freeEnergy_stripeBrick2D_bddAbove`, and `stripeBrick2D_one_card_ne_zero`. -/
theorem freeEnergy_stripeBrick2D_tendsto
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)) p)
      Filter.atTop (nhds L) :=
  Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive
    (IsingModel.latticeGraph 2) (stripeBrick2D w) p
    (stripeBrick2D_card_add w)
    (log_partitionFunctionΛ_stripeBrick2D_super_additive w p hf)
    (freeEnergy_stripeBrick2D_bddAbove w p)
    (stripeBrick2D_one_card_ne_zero hw)

/-! ## Named infinite-volume limit and J=0 closed form -/

/-- **Infinite-volume free-energy density along the 2D stripe
sequence** (fixed width `w ≠ 0`). The `Classical.choose` witness of
`freeEnergy_stripeBrick2D_tendsto`. -/
noncomputable def freeEnergyInfinite_stripeBrick2D
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) : ℝ :=
  Classical.choose (freeEnergy_stripeBrick2D_tendsto hw p hf)

/-- **Convergence to the named limit**. -/
theorem freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_stripeBrick2D hw p hf)) :=
  Classical.choose_spec (freeEnergy_stripeBrick2D_tendsto hw p hf)

/-- **`stripeBrick2D w n` is nonempty** when `w ≠ 0` and `n ≥ 1`.
Derived from `stripeBrick2D_card = n * w`. -/
theorem stripeBrick2D_nonempty {w : ℕ} (hw : w ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (stripeBrick2D w n).Nonempty := by
  rw [← Finset.card_pos, stripeBrick2D_card]
  exact Nat.mul_pos hn (Nat.pos_of_ne_zero hw)

/-- **J=0 closed form for the 2D stripe infinite-volume free-energy
density**: `freeEnergyInfinite_stripeBrick2D hw ⟨0, h, β⟩ hf
= log(2·cosh(β·h))` under ferromagnetic `0 ≤ h, 0 < β`. -/
theorem freeEnergyInfinite_stripeBrick2D_J_zero
    {w : ℕ} (hw : w ≠ 0) {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_stripeBrick2D hw
        (⟨0, h, β⟩ : IsingParams ℝ) ⟨le_refl 0, hh, hβ⟩
      = Real.log (2 * Real.cosh (β * h)) := by
  have hconst : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (stripeBrick2D w n)) (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hne : (stripeBrick2D w n).Nonempty := stripeBrick2D_nonempty hw hn
    have hpos : 0 < Fintype.card (↑(stripeBrick2D w n) : Type _) := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
    exact (IsingModel.freeEnergy_J_zero _ h β hpos).symm
  exact tendsto_nhds_unique
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ _) hconst

/-- **Infinite-volume lower bound** on the 2D stripe. -/
theorem freeEnergyInfinite_stripeBrick2D_ge_log_two
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite_stripeBrick2D hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (stripeBrick2D w n).Nonempty := stripeBrick2D_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(stripeBrick2D w n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Infinite-volume upper bound** on the 2D stripe. -/
theorem freeEnergyInfinite_stripeBrick2D_le
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_stripeBrick2D hw p hf
      ≤ Real.log 2 + |p.β| * (2 * |p.J| + |p.h|) := by
  refine le_of_tendsto
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards with n
  exact stripeBrick2D_freeEnergy_le w n p

/-- **Infinite-volume sandwich** on the 2D stripe (ferromagnetic). -/
theorem freeEnergyInfinite_stripeBrick2D_sandwich
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
        ≤ freeEnergyInfinite_stripeBrick2D hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_stripeBrick2D hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (2 * |J| + |h|) :=
  ⟨freeEnergyInfinite_stripeBrick2D_ge_log_two hw hJ hh hβ,
   freeEnergyInfinite_stripeBrick2D_le hw _ ⟨hJ, hh, hβ⟩⟩

end Concrete

end IsingModel
