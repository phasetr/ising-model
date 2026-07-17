import IsingModel.Concrete.CenteredSlab.InfiniteVolumeLimit

/-!
# Centered slab split — 1D / slab-brick / stripe-brick consistency

Part of the split `IsingModel.Concrete.CenteredSlab` development.
-/

namespace IsingModel

namespace Concrete

variable {d : ℕ}

/-! ## 1D consistency: `centeredSlab (d=0) = shift_(-n) (linearBox (2n))`

The `d = 0` centered slab is, at each index `n`, a negative-`n` shift
of the 1D linearBox at doubled index `2n`. Hence the centeredSlab
Fekete limit (at `d = 0`) coincides with the linearBox Fekete limit. -/

/-- **Finset identity**: `centeredSlab (d=0) Fin.elim0 n` equals the
`-n` coord-0 shift of `linearBox (2n)`. Corresponds to the interval
identity `[-n, n) = shift_(-n) [0, 2n)` on the sole coord. -/
theorem centeredSlab_elim0_eq_shift_linearBox (n : ℕ) :
    @centeredSlab 0 Fin.elim0 n
      = Ambient.vaddFinset
          ((fun _ : Fin 1 => -(n : ℤ)) : Fin 1 → ℤ) (linearBox (2 * n)) := by
  ext v
  rw [mem_centeredSlab, Ambient.mem_vaddFinset]
  constructor
  · intro h
    obtain ⟨⟨hv0a, hv0b⟩, _⟩ := h
    refine ⟨fun _ : Fin 1 => v 0 + (n : ℤ), ?_, ?_⟩
    · rw [mem_linearBox]
      refine ⟨?_, ?_⟩
      · linarith
      · push_cast; linarith
    · funext i
      refine Fin.cases ?_ (fun j : Fin 0 => j.elim0) i
      -- Coord 0: `(-n) + (v 0 + n) = v 0`.
      change ((fun _ : Fin 1 => -(n : ℤ)) +ᵥ
          (fun _ : Fin 1 => v 0 + (n : ℤ))) 0 = v 0
      simp only [vadd_eq_add, Pi.add_apply]
      ring
  · intro h
    obtain ⟨u, hu, huv⟩ := h
    rw [mem_linearBox] at hu
    have hv0 : v 0 = -(n : ℤ) + u 0 := by
      have : ((fun _ : Fin 1 => -(n : ℤ)) +ᵥ u) 0 = v 0 := congrArg (· 0) huv
      simp [vadd_eq_add] at this; linarith
    refine ⟨⟨?_, ?_⟩, fun j => j.elim0⟩
    · linarith
    · have : u 0 < (2 * n : ℤ) := by push_cast at hu; linarith [hu.2]
      linarith

/-- **Finset identity (general d)**: `centeredSlab widths n` equals
the `-n` coord-0 shift of `slabBrick widths (2n)`. Interval identity
`[-n, n) × ∏ [0, widths j) = shift_(-n) ([0, 2n) × ∏ [0, widths j))`. -/
theorem centeredSlab_eq_shift_slabBrick (widths : Fin d → ℕ) (n : ℕ) :
    centeredSlab widths n
      = Ambient.vaddFinset (shiftCoord0Int (d := d) (-(n : ℤ)))
          (slabBrick widths (2 * n)) := by
  ext v
  rw [mem_centeredSlab, Ambient.mem_vaddFinset]
  constructor
  · intro h
    obtain ⟨⟨hv0a, hv0b⟩, hj⟩ := h
    refine ⟨Fin.cases (v 0 + (n : ℤ)) (fun j : Fin d => v j.succ), ?_, ?_⟩
    · rw [mem_slabBrick]
      refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · simp only [Fin.cases_zero]; linarith
      · simp only [Fin.cases_zero]; push_cast; linarith
      · simp only [Fin.cases_succ]; exact hj j
    · funext i
      refine Fin.cases ?_ ?_ i
      · -- Coord 0: `(-n) + (v 0 + n) = v 0`.
        change ((shiftCoord0Int (d := d) (-(n : ℤ))) +ᵥ
            (Fin.cases (v 0 + (n : ℤ)) (fun j : Fin d => v j.succ)
              : Fin (d + 1) → ℤ)) 0 = v 0
        simp only [shiftCoord0Int_zero, Fin.cases_zero, vadd_eq_add,
          Pi.add_apply]
        ring
      · intro j
        -- Coord j.succ: `0 + v j.succ = v j.succ`.
        change ((shiftCoord0Int (d := d) (-(n : ℤ))) +ᵥ
            (Fin.cases (v 0 + (n : ℤ)) (fun k : Fin d => v k.succ)
              : Fin (d + 1) → ℤ)) j.succ = v j.succ
        simp only [shiftCoord0Int_succ, Fin.cases_succ, vadd_eq_add,
          Pi.add_apply, zero_add]
  · intro h
    obtain ⟨u, hu, huv⟩ := h
    rw [mem_slabBrick] at hu
    obtain ⟨⟨hu0a, hu0b⟩, huj⟩ := hu
    have hv0 : v 0 = -(n : ℤ) + u 0 := by
      have : (shiftCoord0Int (d := d) (-(n : ℤ)) +ᵥ u) 0 = v 0 :=
        congrArg (· 0) huv
      simp [vadd_eq_add] at this; linarith
    have hvj : ∀ j : Fin d, v j.succ = u j.succ := by
      intro j
      have : (shiftCoord0Int (d := d) (-(n : ℤ)) +ᵥ u) j.succ = v j.succ :=
        congrArg (· j.succ) huv
      simp [vadd_eq_add] at this; linarith
    refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · linarith
    · have : u 0 < (2 * n : ℤ) := by push_cast at hu0b; linarith
      linarith
    · rw [hvj j]; exact huj j

/-- **Limit equivalence (general d)**: the centered-slab Fekete limit
equals the single-sided `slabBrick` Fekete limit (for the same
`widths`). Proof: per-stage identity via `centeredSlab_eq_shift_slabBrick`
+ translation invariance + subsequence convergence of `slabBrick` at
doubled index `2n`. -/
theorem freeEnergyInfinite_centeredSlab_eq_slabBrick
    {widths : Fin d → ℕ} (hw : ∀ j : Fin d, widths j ≠ 0)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_centeredSlab hw p hf
      = freeEnergyInfinite_slabBrick hw p hf := by
  -- Per-stage: `freeEnergy (centeredSlab widths n) = freeEnergy (slabBrick widths (2n))`.
  have hperStage : ∀ n : ℕ,
      IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (centeredSlab widths n)) p
      = IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths (2 * n))) p := by
    intro n
    rw [centeredSlab_eq_shift_slabBrick]
    exact Ambient.freeEnergyΛ_vaddFinset_eq
      (IsingModel.latticeGraph (d + 1)) _ (slabBrick widths (2 * n)) p
  have htwice : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr (fun b => ?_)
    refine Filter.eventually_atTop.mpr ⟨b, fun n hn => ?_⟩
    linarith
  have h2 : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths (2 * n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_slabBrick hw p hf)) :=
    (freeEnergy_slabBrick_tendsto_freeEnergyInfinite hw p hf).comp htwice
  have h1' : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (d + 1))
          (slabBrick widths (2 * n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_centeredSlab hw p hf)) := by
    refine (freeEnergy_centeredSlab_tendsto_freeEnergyInfinite hw p hf).congr ?_
    intro n; exact hperStage n
  exact tendsto_nhds_unique h1' h2

/-- **Limit equivalence (d=0)**: the centered-slab Fekete limit at
`d = 0, widths = Fin.elim0` equals the 1D linearBox Fekete limit.

Proof via per-stage identity
`freeEnergy (centeredSlab Fin.elim0 n) = freeEnergy (linearBox (2n))`
(from `centeredSlab_elim0_eq_shift_linearBox` + translation invariance
of `freeEnergyΛ`) and subsequence convergence along
`n ↦ 2n` of the linearBox Fekete limit. -/
theorem freeEnergyInfinite_centeredSlab_elim0_eq_linearBox
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    @freeEnergyInfinite_centeredSlab 0 Fin.elim0 (fun j => j.elim0) p hf
      = freeEnergyInfinite_linearBox p hf := by
  -- Per-stage: `freeEnergy (centered Fin.elim0 n) = freeEnergy (linearBox (2n))`.
  have hperStage : ∀ n : ℕ,
      IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph (0 + 1))
          (@centeredSlab 0 Fin.elim0 n)) p
      = IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (linearBox (2 * n))) p := by
    intro n
    rw [centeredSlab_elim0_eq_shift_linearBox]
    exact Ambient.freeEnergyΛ_vaddFinset_eq
      (IsingModel.latticeGraph 1) _ (linearBox (2 * n)) p
  -- Subsequence tendsto at `2·`.
  have htwice : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr (fun b => ?_)
    refine Filter.eventually_atTop.mpr ⟨b, fun n hn => ?_⟩
    linarith
  -- The doubled-index linearBox sequence tendsto `freeEnergyInfinite_linearBox`.
  have h2 : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (linearBox (2 * n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) :=
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf).comp htwice
  -- Transport the centered-slab tendsto to the doubled linearBox sequence.
  have h1' : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (linearBox (2 * n))) p)
      Filter.atTop
      (nhds (@freeEnergyInfinite_centeredSlab 0 Fin.elim0
                (fun j => j.elim0) p hf)) := by
    refine (@freeEnergy_centeredSlab_tendsto_freeEnergyInfinite 0 Fin.elim0
              (fun j => j.elim0) p hf).congr ?_
    intro n
    exact hperStage n
  exact tendsto_nhds_unique h1' h2

/-- **Limit equivalence (d=1)**: the centered-slab Fekete limit at
`d = 1, widths = fun _ => w` equals the 2D `stripeBrick2D w` Fekete
limit. Immediate from transitivity via `freeEnergyInfinite_centeredSlab_eq_slabBrick`
(PR #655) and `freeEnergyInfinite_stripeBrick2D_eq_slabBrick` (PR #651). -/
theorem freeEnergyInfinite_centeredSlab_d_one_eq_stripeBrick2D
    {w : ℕ} (hw : w ≠ 0) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    @freeEnergyInfinite_centeredSlab 1 (fun _ : Fin 1 => w)
        (fun _ => hw) p hf
      = freeEnergyInfinite_stripeBrick2D hw p hf := by
  rw [freeEnergyInfinite_centeredSlab_eq_slabBrick
        (widths := fun _ : Fin 1 => w)]
  exact (freeEnergyInfinite_stripeBrick2D_eq_slabBrick hw p hf).symm


end Concrete

end IsingModel
