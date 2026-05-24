import IsingModel.Concrete.SlabBrick.Geometry

/-!
# Slab brick split — super-additivity, Fekete convergence, and low-dim finite equivalences

Part of the split slab-brick free-energy layer (Issue #1850).
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

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


end Concrete

end IsingModel
