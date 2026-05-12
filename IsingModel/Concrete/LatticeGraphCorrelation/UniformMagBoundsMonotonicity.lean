import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag

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

end Ambient

end IsingModel
