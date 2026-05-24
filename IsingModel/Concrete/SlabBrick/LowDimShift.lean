import IsingModel.Concrete.SlabBrick.InfiniteVolume

/-!
# Slab brick split — low-dim infinite-volume equivalences and translation invariance

Part of the split slab-brick free-energy layer (Issue #1850).
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

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


end Concrete

end IsingModel
