import IsingModel.Concrete.StripeBrick2D.Fekete

namespace IsingModel

namespace Concrete

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

/-- **Translation-invariance of the Fekete limit** on the 2D stripe:
any coord-shift of the stripe sequence converges to the same
`freeEnergyInfinite_stripeBrick2D hw p hf`. -/
theorem freeEnergyInfinite_stripeBrick2D_tendsto_shift
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (t : Fin 2 → ℤ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 2)
          (Ambient.vaddFinset t (stripeBrick2D w n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_stripeBrick2D hw p hf)) := by
  refine (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw p hf).congr ?_
  intro n
  exact (Ambient.freeEnergyΛ_vaddFinset_eq
    (IsingModel.latticeGraph 2) t (stripeBrick2D w n) p).symm

/-- **Nonnegativity** of `freeEnergyInfinite_stripeBrick2D` under
ferromagnetic parameters. -/
theorem freeEnergyInfinite_stripeBrick2D_nonneg
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite_stripeBrick2D hw p hf := by
  refine ge_of_tendsto
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw p hf) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (stripeBrick2D w n).Nonempty := stripeBrick2D_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(stripeBrick2D w n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_nonneg_of_ferromagnetic _ p hf hpos

/-- **Tighter lower bound** `log(2·cosh(β·h)) ≤ freeEnergyInfinite_stripeBrick2D`. -/
theorem freeEnergyInfinite_stripeBrick2D_ge_log_two_cosh
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyInfinite_stripeBrick2D hw
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_stripeBrick2D_tendsto_freeEnergyInfinite hw _ ⟨hJ, hh, hβ⟩) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (stripeBrick2D w n).Nonempty := stripeBrick2D_nonempty hw hn
  have hpos : 0 < Fintype.card (↑(stripeBrick2D w n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hpos

/-- **Cosh-form sandwich** on the 2D stripe. -/
theorem freeEnergyInfinite_stripeBrick2D_sandwich_cosh
    {w : ℕ} (hw : w ≠ 0) {J h β : ℝ}
    (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
        ≤ freeEnergyInfinite_stripeBrick2D hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_stripeBrick2D hw
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (2 * |J| + |h|) :=
  ⟨freeEnergyInfinite_stripeBrick2D_ge_log_two_cosh hw hJ hh hβ,
   freeEnergyInfinite_stripeBrick2D_le hw _ ⟨hJ, hh, hβ⟩⟩

end Concrete

end IsingModel
