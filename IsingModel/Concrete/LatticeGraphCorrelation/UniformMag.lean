import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
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

/-- **`truncated2TwoPoint ≤ 1`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ 1`.

Upper bound: from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261), `twoPointFunction ≤ 1` (PR #260), and `M² ≥ 0`, we get
`truncated2TwoPoint ≤ 1 − 0 = 1`. -/
theorem truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ 1 := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_upper := twoPointFunction_le_one d p r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`-1 ≤ truncated2TwoPoint`** (ferromagnetic): from
`truncated2TwoPoint_nonneg`. -/
theorem neg_one_le_truncated2TwoPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    -1 ≤ truncated2TwoPoint d p r := by
  have := truncated2TwoPoint_nonneg d p hf r
  linarith

/-- **`|truncated2TwoPoint| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    |truncated2TwoPoint d p r| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_truncated2TwoPoint d p hf r,
    truncated2TwoPoint_le_one d p hf r⟩

/-- **`truncated2TwoPoint² ≤ 1`** (ferromagnetic). -/
theorem truncated2TwoPoint_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ^ 2 ≤ 1 := by
  have h := abs_truncated2TwoPoint_le_one d p hf r
  have : |truncated2TwoPoint d p r| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **`truncated2TwoPoint ≤ twoPointFunction`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ twoPointFunction d p r`.

Immediate from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261) + `M² ≥ 0`: subtracting a nonneg quantity only decreases.
Physical content: the truncated 2-point function never exceeds the
connected 2-point function. -/
theorem truncated2TwoPoint_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ twoPointFunction d p r := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`truncated2TwoPoint` at `h = 0` equals `twoPointFunction`** (ferromagnetic):
`truncated2TwoPoint d ⟨J, 0, β⟩ r = twoPointFunction d ⟨J, 0, β⟩ r`.

At zero external field `h = 0`, Z₂ symmetry forces `M = 0`
(`uniformMagnetization_zero_at_h_zero`), so
`truncated2TwoPoint = twoPointFunction − M² = twoPointFunction`. -/
theorem truncated2TwoPoint_h_zero_eq
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) r
      = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      uniformMagnetization_zero_at_h_zero d J β]
  ring

/-- **`truncated2TwoPoint` at `J = 0` vanishes for `r ≠ 0`** (ferromagnetic):
`truncated2TwoPoint d ⟨0, h, β⟩ r = 0`.

At `J = 0` the Ising Hamiltonian has no coupling, so distinct sites are
independent. Consequently `⟨σ_0 σ_r⟩ = ⟨σ_0⟩⟨σ_r⟩ = M²`, and the
truncated 2-point function vanishes. Computation:
`truncated2TwoPoint = twoPointFunction − M² = tanh(βh)² − tanh(βh)² = 0`.
-/
theorem truncated2TwoPoint_J_zero_of_ne_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    truncated2TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r = 0 := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      twoPointFunction_J_zero_of_ne_zero d h β hf hr,
      uniformMagnetization_J_zero d h β hf]
  ring

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

/-- **ℤ^d correlationInfinite J-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

/-- **ℤ^d correlationInfinite h-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d correlationInfinite β-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A

/-- **ℤ^d correlationAlongExhaustion J-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ A hJ₁ hJ₁₂ n

/-- **ℤ^d correlationAlongExhaustion h-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ A hh₁ hh₁₂ n

/-- **ℤ^d correlationAlongExhaustion β-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh A hβ₁ hβ₁₂ n

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

/-- **ℤ^d magnetizationAlongExhaustion ≤ 1** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ≤ 1 :=
  magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf i n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** per stage
(ferromagnetic): stage-wise upper bound by the limsup value. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_magnetizationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion → magnetizationInfinite** (ferromagnetic):
Concrete specialization of `tendsto_magnetizationAlongExhaustion_magnetizationInfinite`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (magnetizationInfinite (IsingModel.latticeGraph d) Λ p i)) :=
  tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d existential convergence of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    ∃ L : ℝ, Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop (nhds L) :=
  magnetizationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d stage-index monotonicity of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Monotone (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i) :=
  magnetizationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion` bounded above** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddAbove (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationAlongExhaustion` bounded below** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddBelow (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` bounded above** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion` monotone** (ferromagnetic):
volume-increasing ⇒ correlation nondecreasing. -/
theorem correlationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d `correlationAlongExhaustion` existential convergence**
(ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop (nhds L) :=
  correlationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d `magnetizationAlongExhaustion` bounded below** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddBelow (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationAlongExhaustion → ⨆ n ...** (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p i n)) :=
  magnetizationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite = ⨆ n, magnetizationAlongExhaustion`. -/
theorem magnetizationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = ⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationInfinite` as `ciSup`**. -/
theorem correlationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      = ⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** pointwise. -/
theorem correlationAlongExhaustion_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** pointwise. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationΛ h-monotonicity**: `MonotoneOn` in `h` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun h : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationΛ β-monotonicity**: `MonotoneOn` in `β` on `Ioi 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : ↑Λ) :
    MonotoneOn
      (fun β : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi 0) :=
  magnetizationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-- **ℤ^d magnetizationΛ J-monotonicity**: `MonotoneOn` in `J` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun J : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-- **ℤ^d magnetizationAlongExhaustion h-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ i hh₁ hh₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion β-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh i hβ₁ hβ₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion J-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ i hJ₁ hJ₁₂ n

/-- **ℤ^d magnetizationΛ at h = 0 vanishes (Z₂)**. -/
theorem magnetizationΛ_latticeGraph_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationAlongExhaustion at h = 0 vanishes (Z₂)** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d magnetizationΛ vanishes at β=0**. -/
theorem magnetizationΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at β=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d magnetizationΛ vanishes at J=h=0**. -/
theorem magnetizationΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_zero_params (IsingModel.latticeGraph d) Λ β i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at J=h=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β i n

/-- **ℤ^d magnetizationΛ at J=0 closed form**: `= tanh(β·h)`. -/
theorem magnetizationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  magnetizationΛ_J_zero (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d magnetizationAlongExhaustion at J=0** per stage (on-stage):
`i ∈ Λ.volume n ⇒ = tanh(β·h)`. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_of_mem (IsingModel.latticeGraph d) Λ h β hi

/-- **ℤ^d magnetizationAlongExhaustion at J=0 is eventually `tanh(β·h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (i : Fin d → ℤ) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d pointwise `|correlationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d pointwise `|magnetizationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ≤ 1 :=
  abs_magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `|correlationInfinite| ≤ 1`** (unconditional). -/
theorem abs_correlationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    |correlationInfinite (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** (unconditional). -/
theorem abs_magnetizationInfinite_latticeGraph_le_one_unconditional
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `-1 ≤ correlationΛ`**. -/
theorem neg_one_le_correlationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationΛ (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `-1 ≤ correlationAlongExhaustion`** per stage. -/
theorem neg_one_le_correlationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    -1 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  neg_one_le_correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `-1 ≤ correlationInfinite`** (unconditional). -/
theorem neg_one_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    -1 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationΛ² ≤ 1`**. -/
theorem correlationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion² ≤ 1`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ^ 2 ≤ 1 :=
  correlationAlongExhaustion_sq_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationInfinite² ≤ 1`**. -/
theorem correlationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `-1 ≤ magnetizationΛ`**. -/
theorem neg_one_le_magnetizationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    -1 ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationΛ (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `-1 ≤ magnetizationAlongExhaustion`** per stage. -/
theorem neg_one_le_magnetizationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    -1 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  neg_one_le_magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `-1 ≤ magnetizationInfinite`** (unconditional). -/
theorem neg_one_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    -1 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite at h = 0 site-wise**:
`magnetizationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i = 0`. -/
theorem magnetizationInfinite_latticeGraph_zero_at_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i = 0 :=
  magnetizationInfinite_zero_at_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationInfinite at β = 0 site-wise**. -/
theorem magnetizationInfinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, 0⟩ i = 0 :=
  magnetizationInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationInfinite at J = 0 site-wise** (ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i
      = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d magnetizationInfinite exhaustion-independence**:
any two exhaustions of `Fin d → ℤ` yield the same ∞-vol magnetization. -/
theorem magnetizationInfinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = magnetizationInfinite (IsingModel.latticeGraph d) Λ' p i :=
  magnetizationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i

/-- **ℤ^d empty-set correlation is 1**: `correlationInfinite ... p ∅ = 1`.
Gibbs-measure normalisation — an empty spin product is `1`. -/
@[simp]
theorem correlationInfinite_latticeGraph_cubicExhaustion_empty
    (d : ℕ) (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p

/-- **ℤ^d GKS-II at ∞-vol** (any-Exhaustion): for ferromagnetic `p`,
`⟨σ^A⟩·⟨σ^B⟩ ≤ ⟨σ^{A ∆ B}⟩` at ∞-volume. -/
theorem correlationInfinite_latticeGraph_gks_second
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      * correlationInfinite (IsingModel.latticeGraph d) Λ p B
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p (A ∆ B) :=
  correlationInfinite_gks_second (IsingModel.latticeGraph d) Λ p hf A B

/-- **ℤ^d FKG for spinProducts at ∞-vol** (any-Exhaustion): alias of
GKS-II form. -/
theorem correlationInfinite_latticeGraph_fkg_spinProduct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      * correlationInfinite (IsingModel.latticeGraph d) Λ p B
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p (A ∆ B) :=
  correlationInfinite_fkg_spinProduct (IsingModel.latticeGraph d) Λ p hf A B

/-- **ℤ^d FKG for spinProducts at ∞-vol** (Glimm–Jaffe §4.4 p. 67):
alias of the `correlationInfinite_gks_second` GKS-II form. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_fkg_spinProduct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A
      * correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p B
      ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (A ∆ B) :=
  correlationInfinite_fkg_spinProduct (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A B

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationΛ`**:
odd-cardinality spin product vanishes at h=0. -/
theorem correlationΛ_latticeGraph_odd_vanish_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A = 0 :=
  correlationΛ_odd_vanish_h_zero (IsingModel.latticeGraph d) Λ J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`** stage-wise. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A n = 0 :=
  correlationAlongExhaustion_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd n

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationInfinite`**:
`correlationInfinite ⟨J, 0, β⟩ A = 0` for any `A` of odd cardinality. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A = 0 :=
  correlationInfinite_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationInfinite`** (any-Exhaustion):
`correlationInfinite ⟨J, 0, β⟩ A = 0` for any `A` of odd cardinality. -/
theorem correlationInfinite_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A = 0 :=
  correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`**
(any-Exhaustion, stage-wise). -/
theorem correlationAlongExhaustion_latticeGraph_any_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A n = 0 :=
  correlationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β A hodd n

/-- **ℤ^d Cor 4.3.5 at ∞-volume** (GJ §4.3 Cor 4.3.5 p. 62, any-Exhaustion):
inductive (n+2)-point bound at `h = 0`. -/
theorem correlationInfinite_latticeGraph_cor_4_3_5_h0
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (Fin d → ℤ)) {j k : Fin d → ℤ}
    (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β⟩ (insert j (insert k S))
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ S *
          correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ {j, k} +
        ∑ T ∈ S.powerset,
          correlationInfinite (IsingModel.latticeGraph d) Λ
              ⟨J, 0, β⟩ (insert j T) *
            correlationInfinite (IsingModel.latticeGraph d) Λ
              ⟨J, 0, β⟩ (insert k (S \ T)) :=
  correlationInfinite_cor_4_3_5_h0
    (IsingModel.latticeGraph d) Λ J β hf S hj hk hjk

/-- **ℤ^d Cor 4.3.5 at ∞-volume** (Glimm–Jaffe §4.3 Cor 4.3.5 p. 62):
inductive (n+2)-point bound at `h = 0` on ℤ^d. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_cor_4_3_5_h0
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (Fin d → ℤ)) {j k : Fin d → ℤ}
    (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j (insert k S))
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ S *
          correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ {j, k} +
        ∑ T ∈ S.powerset,
          correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j T) *
            correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert k (S \ T)) :=
  correlationInfinite_cor_4_3_5_h0 (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf S hj hk hjk

/-- **ℤ^d susceptibilityInfinite at J = 0 site-wise** (Step 261, ferromagnetic). -/
theorem susceptibilityInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  susceptibilityInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d susceptibilityInfinite at β = 0 site-wise** (Step 261). -/
theorem susceptibilityInfinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, 0⟩ i = 0 :=
  susceptibilityInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d susceptibilityInfinite at J = h = 0 site-wise** (Step 261). -/
theorem susceptibilityInfinite_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, 0, β⟩ i = 0 :=
  susceptibilityInfinite_zero_params (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d susceptibilityInfinite ContinuousOn h on Ici 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_continuousOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun h => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ici (0 : ℝ)) :=
  susceptibilityInfinite_continuousOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d susceptibilityInfinite ContinuousOn β on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_continuousOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    ContinuousOn
      (fun β => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_continuousOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

/-- **ℤ^d susceptibilityInfinite DifferentiableOn h on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_differentiableOn_field_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (hβ : 0 < β)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun h => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_differentiableOn_field_J_zero (IsingModel.latticeGraph d) Λ β hβ i

/-- **ℤ^d susceptibilityInfinite DifferentiableOn β on Ioi 0 at J = 0** (Step 265). -/
theorem susceptibilityInfinite_latticeGraph_differentiableOn_beta_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h : ℝ) (hh_nn : 0 ≤ h)
    (i : Fin d → ℤ) :
    DifferentiableOn ℝ
      (fun β => susceptibilityInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i)
      (Set.Ioi (0 : ℝ)) :=
  susceptibilityInfinite_differentiableOn_beta_J_zero (IsingModel.latticeGraph d) Λ h hh_nn i

end Ambient
end IsingModel
