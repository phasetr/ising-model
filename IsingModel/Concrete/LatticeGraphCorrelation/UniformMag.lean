import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# `uniformMagnetization` recasts at ℤ^d
Thin wrappers that express ∞-vol observables (magnetizationInfinite,
truncated2Infinite, susceptibilityInfinite, correlationInfinite, etc.)
in terms of `uniformMagnetization` using translation invariance.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## `uniformMagnetization` recasts -/

/-- **`twoPointFunction` at `r = 0` equals `uniformMagnetization`**
(convenience recast). Combines `twoPointFunction_zero` with the
definition of `uniformMagnetization`. -/
theorem twoPointFunction_zero_eq_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    twoPointFunction d p 0 = uniformMagnetization d p :=
  twoPointFunction_zero d p

/-- **`truncated2TwoPoint = twoPointFunction − (uniformMagnetization)²`**
(convenience recast). -/
theorem truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = twoPointFunction d p r - (uniformMagnetization d p)^2 :=
  truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq d p hf r

/-- **`twoPointFunction ≥ (uniformMagnetization)²`** (convenience recast). -/
theorem twoPointFunction_ge_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (uniformMagnetization d p)^2 ≤ twoPointFunction d p r :=
  twoPointFunction_ge_magnetization_sq d p hf r

/-- **`truncated2TwoPoint` at `J = h = 0` vanishes**:
`truncated2TwoPoint d ⟨0, 0, β⟩ r = 0`. All three Ursell terms vanish. -/
theorem truncated2TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated3TwoPoint` at `J = h = 0` vanishes**:
`truncated3TwoPoint d ⟨0, 0, β⟩ r s = 0`. All seven Ursell terms vanish. -/
theorem truncated3TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s = 0 := by
  unfold truncated3TwoPoint truncated3Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated4TwoPoint` at `J = h = 0` vanishes**:
`truncated4TwoPoint d ⟨0, 0, β⟩ r s u = 0`. All four Lebowitz terms vanish. -/
theorem truncated4TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s u = 0 := by
  unfold truncated4TwoPoint truncated4Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated2TwoPoint` at `β = 0` vanishes**:
`truncated2TwoPoint d ⟨J, h, 0⟩ r = 0`.

At infinite temperature `β = 0` all correlations vanish:
`correlationInfinite ... {0, r} = 0` (PR #278) and the magnetization
term is `0 · 0 = 0` (PR #276). Direct computation. -/
theorem truncated2TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  -- `correlationInfinite ... {0, r} = 0`, `correlationInfinite ... {0} = 0`,
  -- `correlationInfinite ... {r} = 0`.
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring
/-! ## Moved: truncated2TwoPoint bounds + correlation/magnetizationInfinite monotonicity

The 23 ℤ^d `truncated2TwoPoint_*` bounds + trivial slices,
`spontaneousMagnetization_latticeGraph_indep_exhaustion`,
`correlationInfinite_latticeGraph_*` trivial-slice + J/h/β monotone,
`magnetizationInfinite_latticeGraph_*` bound + J/h/β monotone,
and `correlationAlongExhaustion_latticeGraph_*` J/h/β monotone
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagBoundsMonotonicity`.
The legacy import path is preserved by re-importing the new child.
-/

/-- **ℤ^d magnetizationΛ unfolding**: `magnetizationΛ G Λ p i = correlationΛ G Λ p {i}`. -/
theorem magnetizationΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i
      = correlationΛ (IsingModel.latticeGraph d) Λ p {i} :=
  magnetizationΛ_apply (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationΛ ≤ 1** at any site `i : ↑Λ`. -/
theorem magnetizationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationΛ_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `|magnetizationΛ| ≤ 1`** at any site `i : ↑Λ`. -/
theorem abs_magnetizationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    |magnetizationΛ (IsingModel.latticeGraph d) Λ p i| ≤ 1 :=
  abs_magnetizationΛ_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationΛ ≥ 0** for ferromagnetic `p` at any site `i : ↑Λ`. -/
theorem magnetizationΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  magnetizationΛ_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d magnetizationAlongExhaustion unfolding**:
`magnetizationAlongExhaustion G Λ p i n = correlationAlongExhaustion G Λ p {i} n`. -/
theorem magnetizationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {i} n :=
  magnetizationAlongExhaustion_apply (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion `of_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (liftFinset {i} (Finset.singleton_subset_iff.mpr hi)) :=
  magnetizationAlongExhaustion_of_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d magnetizationAlongExhaustion `of_not_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_not_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∉ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n = 0 :=
  magnetizationAlongExhaustion_of_not_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d `magnetizationInfinite_apply`** unfolding. -/
theorem magnetizationInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i} :=
  magnetizationInfinite_apply (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `freeEnergyInfinite_apply`** unfolding (limsup form). -/
theorem freeEnergyInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      = Filter.limsup
          (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
          Filter.atTop :=
  freeEnergyInfinite_apply (IsingModel.latticeGraph d) Λ p
/-! ## Moved: magnetizationAlongExhaustion / correlationAlongExhaustion bounds + convergence wrappers

The 17 ℤ^d `magnetizationAlongExhaustion_latticeGraph_*` and
`correlationAlongExhaustion_latticeGraph_*` bound / monotone /
convergent / bddAbove / bddBelow / `_le_*Infinite` /
`_tendsto_ciSup` / `_eq_ciSup` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergence`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: magnetizationΛ + AlongExhaustion monotone + trivial-slice wrappers

The 15 ℤ^d `magnetizationΛ_latticeGraph_*` and
`magnetizationAlongExhaustion_latticeGraph_*` J/h/β monotonicity +
trivial-slice (h_zero, beta_zero, zero_params, J_zero variants)
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagMagnetizationTrivial`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: abs / neg / sq bounds wrappers

The 13 ℤ^d `abs_*_latticeGraph_le_one` /
`neg_one_le_*_latticeGraph` / `*_latticeGraph_sq_le_one` wrappers
(for `correlationΛ`, `correlationAlongExhaustion`,
`correlationInfinite`, `magnetizationΛ`,
`magnetizationAlongExhaustion`, `magnetizationInfinite`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAbsBounds`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: correlation trivial / GKS-II / FKG / h_zero / cor 4.3.5 wrappers

The 15 ℤ^d wrappers covering `magnetizationInfinite_latticeGraph_*`
trivial slices, `correlationInfinite_latticeGraph_*` empty / GKS-II
/ FKG / h_zero / cor_4_3_5_h0, and
`correlationΛ_latticeGraph_odd_vanish_h_zero` /
`correlationAlongExhaustion_latticeGraph_*_h_zero` wrappers now live
in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivial`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **ℤ^d spontaneousMagnetization at J = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ 0 β i = 0 :=
  spontaneousMagnetization_J_zero (IsingModel.latticeGraph d) Λ hβ i

/-- **ℤ^d spontaneousMagnetization at β = 0 vanishes** (Step 269). -/
theorem spontaneousMagnetization_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J 0 i = 0 :=
  spontaneousMagnetization_beta_zero (IsingModel.latticeGraph d) Λ J i

/-- **ℤ^d spontaneousCorrelation at J = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ 0 β A = 0 :=
  spontaneousCorrelation_J_zero (IsingModel.latticeGraph d) Λ hβ A hA

/-- **ℤ^d spontaneousCorrelation at β = 0 general nonempty A** (Step 272). -/
theorem spontaneousCorrelation_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J 0 A = 0 :=
  spontaneousCorrelation_beta_zero (IsingModel.latticeGraph d) Λ J A hA

/-- **ℤ^d spontaneousCorrelation at empty A is 1** (Step 274). -/
theorem spontaneousCorrelation_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β
        (∅ : Finset (Fin d → ℤ)) = 1 :=
  spontaneousCorrelation_empty (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d correlationInfinite at J = h = 0 vanishes for nonempty A** (Step 280). -/
theorem correlationInfinite_latticeGraph_zero_params_vanish_of_nonempty_A
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) {β : ℝ} (hβ : 0 < β)
    {A : Finset (Fin d → ℤ)} (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ ⟨0, 0, β⟩ A = 0 :=
  correlationInfinite_zero_params_vanish_of_nonempty_A
    (IsingModel.latticeGraph d) Λ hβ hA

end Ambient
end IsingModel
