import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagRecasts
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFunctionTrivialSlices

/-!
# ℤ^d truncated2TwoPoint bounds + correlation/magnetizationInfinite monotonicity wrappers

Narrow child module for 23 ℤ^d wrappers covering:

- `truncated2TwoPoint_*` bounds: `le_one`, `neg_one_le`, `abs_le_one`,
  `sq_le_one`, `le_twoPointFunction`, `h_zero_eq`, `J_zero_of_ne_zero`;
- `spontaneousMagnetization_latticeGraph_indep_exhaustion`;
- `correlationInfinite_latticeGraph_*` trivial slices (`J_zero`,
  `beta_zero_vanish`, `zero_params_vanish`) and J / h / β monotone;
- `magnetizationInfinite_latticeGraph_*` bounds (`le_one`, `nonneg`)
  and J / h / β monotone;
- `correlationAlongExhaustion_latticeGraph_*` J / h / β monotone.

Theorem names are unchanged from the former `UniformMag`
declarations.
-/

namespace IsingModel
namespace Ambient


/-! ## Moved: truncated2TwoPoint bound wrappers

The seven wrappers `truncated2TwoPoint_le_one`,
`neg_one_le_truncated2TwoPoint`, `abs_truncated2TwoPoint_le_one`,
`truncated2TwoPoint_sq_le_one`,
`truncated2TwoPoint_le_twoPointFunction`,
`truncated2TwoPoint_h_zero_eq`, and
`truncated2TwoPoint_J_zero_of_ne_zero`
now live in `UniformMagBoundsTruncated2TwoPoint.lean`. -/

/-- **ℤ^d spontaneousMagnetization exhaustion-independence**:
any two exhaustions yield the same `spontaneousMagnetization`. -/
theorem spontaneousMagnetization_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β i :=
  spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ i

/-- **ℤ^d correlationInfinite at J = 0 general-A closed form** (ferromagnetic):
`correlationInfinite (latticeGraph d) Λ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf A

/-- **ℤ^d correlationInfinite at β = 0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_beta_zero_vanish (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d correlationInfinite at J=h=0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_zero_params_vanish (IsingModel.latticeGraph d) Λ β A hA

/-- **ℤ^d magnetizationInfinite ≤ 1** site-wise (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite ≥ 0** site-wise (any Exhaustion, ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d magnetizationInfinite J-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-- **ℤ^d magnetizationInfinite h-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationInfinite β-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-! ## Moved: correlationInfinite monotonicity wrappers

The three wrappers
`correlationInfinite_latticeGraph_monotone_{J,h,beta}` now live in
`UniformMagBoundsCorrInfMonotone.lean`. -/

/-! ## Moved: correlationAlongExhaustion monotonicity wrappers

The three wrappers
`correlationAlongExhaustion_latticeGraph_monotone_{J,h,beta}`
now live in `UniformMagBoundsCorrAlongExMonotone.lean`. -/


/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** site-wise (any Exhaustion, ferromagnetic):
combines `magnetizationInfinite_latticeGraph_nonneg` (so `0 ≤ M`, hence
`-1 ≤ M`) with `magnetizationInfinite_latticeGraph_le_one`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 := by
  have hl := magnetizationInfinite_latticeGraph_nonneg d Λ p hf i
  have hu := magnetizationInfinite_latticeGraph_le_one d Λ p i
  exact abs_le.mpr ⟨by linarith, hu⟩

end Ambient

end IsingModel
