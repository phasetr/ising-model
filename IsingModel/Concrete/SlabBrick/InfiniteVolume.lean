import IsingModel.Concrete.SlabBrick.Fekete

/-!
# Slab brick split — sandwich bounds and the named infinite-volume limit

Part of the split slab-brick free-energy layer (Issue #1850).
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

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


end Concrete

end IsingModel
