import IsingModel.Concrete.StripeBrick2D.Geometry

namespace IsingModel

namespace Concrete

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


end Concrete

end IsingModel
