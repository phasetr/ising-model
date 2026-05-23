import IsingModel.Concrete.CenteredSlab.Geometry

/-!
# Centered slab split — super-additivity, BddAbove, Fekete convergence, sandwich

Part of the split `IsingModel.Concrete.CenteredSlab` development.
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

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


end Concrete

end IsingModel
