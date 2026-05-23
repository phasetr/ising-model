import IsingModel.Concrete.CenteredSlab.Fekete

/-!
# Centered slab split — named infinite-volume limit and bound properties

Part of the split `IsingModel.Concrete.CenteredSlab` development.
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

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

/-- **Nonnegativity** of `freeEnergyInfinite_centeredSlab` under
ferromagnetic parameters. -/
theorem freeEnergyInfinite_centeredSlab_nonneg
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite_centeredSlab hw p hf := by
  refine ge_of_tendsto
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (centeredSlab widths n).Nonempty := centeredSlab_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_nonneg_of_ferromagnetic _ p hf hpos

/-- **Tighter lower bound** `log(2·cosh(β·h)) ≤ freeEnergyInfinite_centeredSlab`. -/
theorem freeEnergyInfinite_centeredSlab_ge_log_two_cosh
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyInfinite_centeredSlab hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ⟩) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (centeredSlab widths n).Nonempty := centeredSlab_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(centeredSlab widths n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hpos

/-- **Cosh-form sandwich** on the centered slab. -/
theorem freeEnergyInfinite_centeredSlab_sandwich_cosh
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
        ≤ freeEnergyInfinite_centeredSlab hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_centeredSlab hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * ((d + 1) * |J| + |h|) :=
  ⟨freeEnergyInfinite_centeredSlab_ge_log_two_cosh hw hJ hh hβ,
   freeEnergyInfinite_centeredSlab_le hw _ ⟨hJ, hh, hβ⟩⟩


end Concrete

end IsingModel
