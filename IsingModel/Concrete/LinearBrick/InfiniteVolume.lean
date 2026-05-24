import IsingModel.Concrete.LinearBrick.Fekete

namespace IsingModel

namespace Concrete

/-! ## Named infinite-volume limit and J=0 closed form -/

/-- **Infinite-volume free-energy density along the 1D linearBox
sequence**. The `Classical.choose` witness of
`freeEnergy_linearBox_tendsto`, pinning down the Fekete limit value. -/
noncomputable def freeEnergyInfinite_linearBox
    (p : IsingParams ℝ) (hf : Ferromagnetic p) : ℝ :=
  Classical.choose (freeEnergy_linearBox_tendsto p hf)

/-- **Convergence to the named limit**: the 1D linearBox
free-energy-density sequence converges to `freeEnergyInfinite_linearBox p hf`. -/
theorem freeEnergy_linearBox_tendsto_freeEnergyInfinite
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) :=
  Classical.choose_spec (freeEnergy_linearBox_tendsto p hf)

/-- **`linearBox n` is nonempty** when `n ≥ 1`. Derived from
`linearBox_card = n`. -/
theorem linearBox_nonempty {n : ℕ} (hn : 1 ≤ n) : (linearBox n).Nonempty := by
  rw [← Finset.card_pos, linearBox_card]; exact hn

/-- **J=0 closed form for the 1D linearBox infinite-volume free-energy
density**: `freeEnergyInfinite_linearBox ⟨0, h, β⟩ hf = log(2·cosh(β·h))`
under ferromagnetic `0 ≤ h, 0 < β`. Parallel to PR #647. -/
theorem freeEnergyInfinite_linearBox_J_zero
    {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_linearBox
        (⟨0, h, β⟩ : IsingParams ℝ) ⟨le_refl 0, hh, hβ⟩
      = Real.log (2 * Real.cosh (β * h)) := by
  have hconst : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n))
          (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hne : (linearBox n).Nonempty := linearBox_nonempty hn
    have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
    exact (IsingModel.freeEnergy_J_zero _ h β hpos).symm
  exact tendsto_nhds_unique
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ _) hconst

/-- **Infinite-volume lower bound** `log 2 ≤ freeEnergyInfinite_linearBox`
for ferromagnetic `0 ≤ J, 0 ≤ h, 0 < β`. Transports the per-stage
`freeEnergy_ge_log_two_of_ferromagnetic` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_ge_log_two
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite_linearBox (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Infinite-volume upper bound**
`freeEnergyInfinite_linearBox ≤ log 2 + |β|·(|J| + |h|)`. Transports
the per-stage `linearBox_freeEnergy_le` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_le
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_linearBox p hf
      ≤ Real.log 2 + |p.β| * (|p.J| + |p.h|) := by
  refine le_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf) ?_
  filter_upwards with n
  exact linearBox_freeEnergy_le n p

/-- **Infinite-volume sandwich** on the 1D linearBox (ferromagnetic):
`log 2 ≤ freeEnergyInfinite_linearBox ≤ log 2 + |β|·(|J| + |h|)`. -/
theorem freeEnergyInfinite_linearBox_sandwich
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
        ≤ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (|J| + |h|) :=
  ⟨freeEnergyInfinite_linearBox_ge_log_two hJ hh hβ,
   freeEnergyInfinite_linearBox_le _ ⟨hJ, hh, hβ⟩⟩

/-- **Translation-invariance of the Fekete limit** on the 1D
linearBox: any coord-shift of the linearBox sequence converges to the
same `freeEnergyInfinite_linearBox p hf`. -/
theorem freeEnergyInfinite_linearBox_tendsto_shift
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Fin 1 → ℤ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (Ambient.vaddFinset t (linearBox n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) := by
  refine (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf).congr ?_
  intro n
  exact (Ambient.freeEnergyΛ_vaddFinset_eq
    (IsingModel.latticeGraph 1) t (linearBox n) p).symm

/-- **Nonnegativity** of `freeEnergyInfinite_linearBox` under
ferromagnetic parameters. Transport per-stage
`freeEnergy_nonneg_of_ferromagnetic` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_nonneg
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite_linearBox p hf := by
  refine ge_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_nonneg_of_ferromagnetic _ p hf hpos

/-- **Tighter lower bound** `log(2·cosh(β·h)) ≤ freeEnergyInfinite_linearBox`
under ferromagnetic `0 ≤ J, 0 ≤ h, 0 < β`. Sharper than
`freeEnergyInfinite_linearBox_ge_log_two` (PR #650) when `h > 0`. -/
theorem freeEnergyInfinite_linearBox_ge_log_two_cosh
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyInfinite_linearBox
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh, hβ⟩) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hpos

/-- **Cosh-form sandwich** on the 1D linearBox: combines the tighter
`log(2·cosh(β·h))` lower bound with the upper bound `log 2 + |β|·(|J| + |h|)`. -/
theorem freeEnergyInfinite_linearBox_sandwich_cosh
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
        ≤ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (|J| + |h|) :=
  ⟨freeEnergyInfinite_linearBox_ge_log_two_cosh hJ hh hβ,
   freeEnergyInfinite_linearBox_le _ ⟨hJ, hh, hβ⟩⟩

end Concrete

end IsingModel
