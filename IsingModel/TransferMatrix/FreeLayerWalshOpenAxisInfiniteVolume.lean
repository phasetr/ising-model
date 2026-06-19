import IsingModel.TransferMatrix.FreeLayerWalshOpenAxisDecay
import IsingModel.AmbientLattice.CorrelationInfinite.Bounds

/-!
# Infinite-volume free-layer axis-graph decay

This file passes the finite free-layer axis-graph cubic-box decay estimates to
the cubic exhaustion and to `correlationInfinite`.  The graph remains the
longitudinal-only `freeLayerAxisGraph`: no transverse nearest-neighbour edges or
interacting transverse layer estimates are claimed here.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-! ## Stagewise free-layer axis bounds -/

/-- The ambient two-point observable on a longitudinal free-layer axis. -/
def freeLayerAxisTwoPoint (d : ℕ) (x : Fin d → ℤ) (sep : ℕ) :
    Finset (Fin (d + 1) → ℤ) :=
  {freeLayerAxisPoint d 0 x, freeLayerAxisPoint d sep x}

/-- Positivity of `tanh a` in the positive coupling-temperature regime. -/
private theorem tanh_pos_of_pos {a : ℝ} (ha : 0 < a) : 0 < Real.tanh a := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr ha) (Real.cosh_pos _)

/-- Finite cubic-box axis decay in `tanh` form, with the transverse coordinate
given as an ambient lattice point known to lie in the transverse cubic box. -/
private theorem finite_freeLayerAxisGraph_axis_abs_le_tanh_of_mem
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (hx : x ∈ Ambient.cubicBox d N)
    (sep : ℕ) (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation (Ambient.inducedGraph (freeLayerAxisGraph d)
      (Ambient.cubicBox (d + 1) N)) p
      (freeLayerOpenCubicAxisTwoPoint d N sep hsepN
        (⟨x, hx⟩ : CubicLayerSite d N))|
      ≤ Real.tanh (p.β * p.J) ^ sep :=
  correlation_induced_freeLayerAxisGraph_cubicBox_same_transverse_abs_le_tanh_clean
    d N p hp hβJ ⟨x, hx⟩ sep hsep hsepN

/-- Finite cubic-box axis decay in mass form, with the transverse coordinate
given as an ambient lattice point known to lie in the transverse cubic box. -/
private theorem finite_freeLayerAxisGraph_axis_abs_le_exp_neg_mass_of_mem
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (hx : x ∈ Ambient.cubicBox d N)
    (sep : ℕ) (hsep : 0 < sep) (hsepN : sep ≤ N) :
    |correlation (Ambient.inducedGraph (freeLayerAxisGraph d)
      (Ambient.cubicBox (d + 1) N)) p
      (freeLayerOpenCubicAxisTwoPoint d N sep hsepN
        (⟨x, hx⟩ : CubicLayerSite d N))|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) :=
  correlation_induced_freeLayerAxisGraph_cubicBox_same_transverse_abs_le_exp_neg_mass
    d N p hp hβJ ⟨x, hx⟩ sep hsep hsepN

/-- The transported finite cubic-box two-point set is the explicit axis pair. -/
private theorem freeLayerOpenCubicAxisTwoPoint_eq_axisPair
    (d N sep : ℕ) (hsepN : sep ≤ N) (x : CubicLayerSite d N) :
    freeLayerOpenCubicAxisTwoPoint d N sep hsepN x =
      ({⟨freeLayerAxisPoint d 0 x.val,
          freeLayerAxisPoint_mem_cubicBox (d := d) (N := N) (t := 0) (x := x.val)
            (by omega) x.property⟩,
        ⟨freeLayerAxisPoint d sep x.val,
          freeLayerAxisPoint_mem_cubicBox (d := d) (N := N) (t := sep) (x := x.val)
            (by omega) x.property⟩} :
        Finset ↑(Ambient.cubicBox (d + 1) N)) := by
  ext y
  simp [freeLayerOpenCubicAxisTwoPoint, freeLayerOpenCubicSlabTwoPoint,
    freeLayerOpenCubicLeftIndex, freeLayerOpenCubicRightIndex,
    freeLayerOpenSlabCubicBoxEquiv, freeLayerOpenSlabCubicBoxPoint]

/-- Stagewise cubic-exhaustion free-layer axis decay in `tanh` form. -/
theorem abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_tanh
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    |Ambient.correlationAlongExhaustion (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep) N|
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  classical
  by_cases hA :
      freeLayerAxisTwoPoint d x sep ⊆ (Ambient.cubicExhaustion (d + 1)).volume N
  · have hmem0 : freeLayerAxisPoint d 0 x ∈ Ambient.cubicBox (d + 1) N := by
      exact hA (by simp [freeLayerAxisTwoPoint])
    have hmemSep : freeLayerAxisPoint d sep x ∈ Ambient.cubicBox (d + 1) N := by
      exact hA (by simp [freeLayerAxisTwoPoint])
    have hx : x ∈ Ambient.cubicBox d N := by
      rw [Ambient.mem_cubicBox] at hmem0 ⊢
      intro j
      simpa [freeLayerAxisPoint] using hmem0 j.succ
    have hsepN : sep ≤ N := by
      have hcoord : -(N : ℤ) ≤ (sep : ℤ) ∧ (sep : ℤ) ≤ N := by
        simpa using (Ambient.mem_cubicBox.mp hmemSep) 0
      omega
    have hfinite :=
      finite_freeLayerAxisGraph_axis_abs_le_tanh_of_mem
        d N p hp hβJ x hx sep hsep hsepN
    have hlift :
        Ambient.liftFinset (freeLayerAxisTwoPoint d x sep) hA =
          freeLayerOpenCubicAxisTwoPoint d N sep hsepN
            (⟨x, hx⟩ : CubicLayerSite d N) := by
      change Ambient.liftFinset
          ({freeLayerAxisPoint d 0 x, freeLayerAxisPoint d sep x} :
            Finset (Fin (d + 1) → ℤ)) hA =
          freeLayerOpenCubicAxisTwoPoint d N sep hsepN
            (⟨x, hx⟩ : CubicLayerSite d N)
      rw [Ambient.liftFinset_pair hA hmem0 hmemSep]
      exact (freeLayerOpenCubicAxisTwoPoint_eq_axisPair d N sep hsepN
        (⟨x, hx⟩ : CubicLayerSite d N)).symm
    have hcorr :
        @Ambient.correlationAlongExhaustion (Fin (d + 1) → ℤ) _
          (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
          (fun _ => CategoryTheory.FinCategory.fintypeObj) p
          (freeLayerAxisTwoPoint d x sep) N =
          @correlation (↑(Ambient.cubicBox (d + 1) N)) _ _
            (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N))
            CategoryTheory.FinCategory.fintypeObj p
            (freeLayerOpenCubicAxisTwoPoint d N sep hsepN
              (⟨x, hx⟩ : CubicLayerSite d N)) := by
      rw [@Ambient.correlationAlongExhaustion_of_subset (Fin (d + 1) → ℤ) _
        (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
        (fun _ => CategoryTheory.FinCategory.fintypeObj) p
        (A := freeLayerAxisTwoPoint d x sep) (n := N) hA,
        Ambient.correlationΛ_apply, hlift]
      rfl
    conv_lhs =>
      arg 1
      rw [hcorr]
    exact hfinite
  · have hzero :
        @Ambient.correlationAlongExhaustion (Fin (d + 1) → ℤ) _
          (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
          (fun _ => CategoryTheory.FinCategory.fintypeObj) p
          (freeLayerAxisTwoPoint d x sep) N = 0 :=
      @Ambient.correlationAlongExhaustion_of_not_subset (Fin (d + 1) → ℤ) _
        (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
        (fun _ => CategoryTheory.FinCategory.fintypeObj) p
        (A := freeLayerAxisTwoPoint d x sep) (n := N) hA
    conv_lhs =>
      arg 1
      rw [hzero]
    simpa using pow_nonneg (tanh_pos_of_pos hβJ).le sep

/-- Stagewise cubic-exhaustion free-layer axis decay in mass form. -/
theorem abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_exp_neg_mass
    (d N : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    |Ambient.correlationAlongExhaustion (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep) N|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  classical
  by_cases hA :
      freeLayerAxisTwoPoint d x sep ⊆ (Ambient.cubicExhaustion (d + 1)).volume N
  · have hmem0 : freeLayerAxisPoint d 0 x ∈ Ambient.cubicBox (d + 1) N := by
      exact hA (by simp [freeLayerAxisTwoPoint])
    have hmemSep : freeLayerAxisPoint d sep x ∈ Ambient.cubicBox (d + 1) N := by
      exact hA (by simp [freeLayerAxisTwoPoint])
    have hx : x ∈ Ambient.cubicBox d N := by
      rw [Ambient.mem_cubicBox] at hmem0 ⊢
      intro j
      simpa [freeLayerAxisPoint] using hmem0 j.succ
    have hsepN : sep ≤ N := by
      have hcoord : -(N : ℤ) ≤ (sep : ℤ) ∧ (sep : ℤ) ≤ N := by
        simpa using (Ambient.mem_cubicBox.mp hmemSep) 0
      omega
    have hfinite :=
      finite_freeLayerAxisGraph_axis_abs_le_exp_neg_mass_of_mem
        d N p hp hβJ x hx sep hsep hsepN
    have hlift :
        Ambient.liftFinset (freeLayerAxisTwoPoint d x sep) hA =
          freeLayerOpenCubicAxisTwoPoint d N sep hsepN
            (⟨x, hx⟩ : CubicLayerSite d N) := by
      change Ambient.liftFinset
          ({freeLayerAxisPoint d 0 x, freeLayerAxisPoint d sep x} :
            Finset (Fin (d + 1) → ℤ)) hA =
          freeLayerOpenCubicAxisTwoPoint d N sep hsepN
            (⟨x, hx⟩ : CubicLayerSite d N)
      rw [Ambient.liftFinset_pair hA hmem0 hmemSep]
      exact (freeLayerOpenCubicAxisTwoPoint_eq_axisPair d N sep hsepN
        (⟨x, hx⟩ : CubicLayerSite d N)).symm
    have hcorr :
        @Ambient.correlationAlongExhaustion (Fin (d + 1) → ℤ) _
          (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
          (fun _ => CategoryTheory.FinCategory.fintypeObj) p
          (freeLayerAxisTwoPoint d x sep) N =
          @correlation (↑(Ambient.cubicBox (d + 1) N)) _ _
            (Ambient.inducedGraph (freeLayerAxisGraph d) (Ambient.cubicBox (d + 1) N))
            CategoryTheory.FinCategory.fintypeObj p
            (freeLayerOpenCubicAxisTwoPoint d N sep hsepN
              (⟨x, hx⟩ : CubicLayerSite d N)) := by
      rw [@Ambient.correlationAlongExhaustion_of_subset (Fin (d + 1) → ℤ) _
        (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
        (fun _ => CategoryTheory.FinCategory.fintypeObj) p
        (A := freeLayerAxisTwoPoint d x sep) (n := N) hA,
        Ambient.correlationΛ_apply, hlift]
      rfl
    conv_lhs =>
      arg 1
      rw [hcorr]
    exact hfinite
  · have hzero :
        @Ambient.correlationAlongExhaustion (Fin (d + 1) → ℤ) _
          (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
          (fun _ => CategoryTheory.FinCategory.fintypeObj) p
          (freeLayerAxisTwoPoint d x sep) N = 0 :=
      @Ambient.correlationAlongExhaustion_of_not_subset (Fin (d + 1) → ℤ) _
        (freeLayerAxisGraph d) (Ambient.cubicExhaustion (d + 1))
        (fun _ => CategoryTheory.FinCategory.fintypeObj) p
        (A := freeLayerAxisTwoPoint d x sep) (n := N) hA
    conv_lhs =>
      arg 1
      rw [hzero]
    simpa using (Real.exp_pos (-(correlationMass (p.β * p.J)) * sep)).le

/-! ## Infinite-volume free-layer axis bounds -/

/-- Infinite-volume free-layer axis decay in absolute-value `tanh` form. -/
theorem abs_correlationInfinite_freeLayerAxisGraph_axis_le_tanh
    (d : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    |Ambient.correlationInfinite (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep)|
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  rw [Ambient.correlationInfinite_eq_ciSup]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h0 :=
      (abs_le.mp
        (abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_tanh
          d 0 p hp hβJ x sep hsep)).1
    exact h0.trans
      (le_ciSup
        (Ambient.correlationAlongExhaustion_bddAbove (freeLayerAxisGraph d)
          (Ambient.cubicExhaustion (d + 1)) p (freeLayerAxisTwoPoint d x sep)) 0)
  · refine ciSup_le ?_
    intro N
    exact (le_abs_self _).trans
      (abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_tanh
        d N p hp hβJ x sep hsep)

/-- Infinite-volume free-layer axis decay in `tanh` form. -/
theorem correlationInfinite_freeLayerAxisGraph_axis_le_tanh
    (d : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    Ambient.correlationInfinite (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep)
      ≤ Real.tanh (p.β * p.J) ^ sep := by
  exact (le_abs_self _).trans
    (abs_correlationInfinite_freeLayerAxisGraph_axis_le_tanh
      d p hp hβJ x sep hsep)

/-- Infinite-volume free-layer axis decay in absolute-value mass form. -/
theorem abs_correlationInfinite_freeLayerAxisGraph_axis_le_exp_neg_mass
    (d : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    |Ambient.correlationInfinite (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep)|
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  rw [Ambient.correlationInfinite_eq_ciSup]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h0 :=
      (abs_le.mp
        (abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_exp_neg_mass
          d 0 p hp hβJ x sep hsep)).1
    exact h0.trans
      (le_ciSup
        (Ambient.correlationAlongExhaustion_bddAbove (freeLayerAxisGraph d)
          (Ambient.cubicExhaustion (d + 1)) p (freeLayerAxisTwoPoint d x sep)) 0)
  · refine ciSup_le ?_
    intro N
    exact (le_abs_self _).trans
      (abs_correlationAlongExhaustion_freeLayerAxisGraph_axis_le_exp_neg_mass
        d N p hp hβJ x sep hsep)

/-- Infinite-volume free-layer axis decay in mass form. -/
theorem correlationInfinite_freeLayerAxisGraph_axis_le_exp_neg_mass
    (d : ℕ) (p : IsingParams ℝ)
    (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin d → ℤ) (sep : ℕ) (hsep : 0 < sep) :
    Ambient.correlationInfinite (freeLayerAxisGraph d)
      (Ambient.cubicExhaustion (d + 1)) p
      (freeLayerAxisTwoPoint d x sep)
      ≤ Real.exp (-(correlationMass (p.β * p.J)) * sep) := by
  exact (le_abs_self _).trans
    (abs_correlationInfinite_freeLayerAxisGraph_axis_le_exp_neg_mass
      d p hp hβJ x sep hsep)

end TransferMatrix

end IsingModel
