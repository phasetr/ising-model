import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG

/-!
# Site-independent magnetization and two-point bounds at ℤ^d

- `uniformMagnetization` definition and basic properties.
- Basic bounds on the ℤ^d two-point functions (`twoPointFunction`).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Site-independent magnetization on ℤ^d -/

/-- **Uniform magnetization on ℤ^d**: since the ∞-vol magnetization is
site-independent on the translation-invariant ℤ^d lattice (PR #257),
we package the value at `0` as a scalar `uniformMagnetization d p`.

`uniformMagnetization d p := magnetizationInfinite (latticeGraph d)
(cubicExhaustion d) p 0`. -/
noncomputable def uniformMagnetization (d : ℕ) (p : IsingParams ℝ) : ℝ :=
  magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **Unfolding of `uniformMagnetization`**:
`uniformMagnetization d p = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0`. -/
theorem uniformMagnetization_apply (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 := rfl

/-- **ℤ^d `uniformMagnetization ≥ tanh(β·h)`** (ferromagnetic). -/
theorem uniformMagnetization_ge_tanh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.tanh (β * h)
      ≤ uniformMagnetization d (⟨J, h, β⟩ : IsingParams ℝ) :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ 0

/-- **`uniformMagnetization` equals `magnetizationInfinite` under any
Exhaustion** (ferromagnetic): bridges the fixed-`cubicExhaustion` form
to arbitrary Exhaustions via `magnetizationInfinite_indep_exhaustion`. -/
theorem uniformMagnetization_eq_magnetizationInfinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d) Λ' p 0 := by
  rw [uniformMagnetization_apply]
  exact magnetizationInfinite_indep_exhaustion (IsingModel.latticeGraph d) _ Λ' p hf 0

/-- **Bridge**: for ferromagnetic `p` and any site `i : Fin d → ℤ`,
`magnetizationInfinite ... p i = uniformMagnetization d p`.

Immediate from `magnetizationInfinite_latticeGraph_cubicExhaustion_eq`
(PR #257) at `i, 0`. -/
@[simp]
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i
      = uniformMagnetization d p :=
  magnetizationInfinite_latticeGraph_cubicExhaustion_eq d p hf i 0

/-- **Nonnegativity of `uniformMagnetization`** (ferromagnetic).
Specialization of the abstract `magnetizationInfinite_nonneg`. -/
theorem uniformMagnetization_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ uniformMagnetization d p :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0

/-- **Upper bound on `uniformMagnetization`**:
`uniformMagnetization d p ≤ 1`. -/
theorem uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`-1 ≤ uniformMagnetization`** unconditionally. Specialization of
`neg_one_le_magnetizationInfinite` at site `0`. -/
theorem neg_one_le_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    -1 ≤ uniformMagnetization d p :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`|uniformMagnetization| ≤ 1`** unconditionally. Specialization of
`abs_magnetizationInfinite_le_one` at site `0`. -/
theorem abs_uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    |uniformMagnetization d p| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`uniformMagnetization² ≤ 1`** unconditionally. Specialization of
`magnetizationInfinite_sq_le_one` at site `0`. -/
theorem uniformMagnetization_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0


/-- **Uniform spontaneous magnetization on ℤ^d**: by site-independence
of spontaneous magnetization on the translation-invariant ℤ^d lattice
(PR #257), we package the value at `0` as a scalar.

`uniformSpontaneousMagnetization d J β := spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
noncomputable def uniformSpontaneousMagnetization
    (d : ℕ) (J β : ℝ) : ℝ :=
  spontaneousMagnetization (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β 0

/-! ## Moved: ℤ^d `uniformSpontaneousMagnetization` wrappers

The 10 ℤ^d `uniformSpontaneousMagnetization*` wrappers
(`_apply`, `_eq_spontaneousMagnetization_any_exhaustion`,
`_monotone_J`, `_monotone_beta`,
`spontaneousMagnetization_latticeGraph_cubicExhaustion_eq_uniform`,
`_nonneg`, `_le_one`, `neg_one_le_*`,
`abs_*_le_one`, `_sq_le_one`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagUniformSpontaneous`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d `spontaneousCorrelation`/`spontaneousMagnetization_latticeGraph` wrappers

The 8 ℤ^d wrappers `spontaneousCorrelation_latticeGraph_apply`,
`spontaneousMagnetization_latticeGraph_apply`,
`neg_one_le_spontaneousMagnetization_latticeGraph`,
`abs_spontaneousMagnetization_latticeGraph_le_one`,
`spontaneousMagnetization_latticeGraph_{nonneg,le_one,monotone_J,monotone_beta}`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagSpontaneous`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **`uniformMagnetization` at `β = 0`**:
`uniformMagnetization d ⟨J, h, 0⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_beta_zero` at site `0`:
at infinite temperature (`β = 0`) all spin correlations vanish, in
particular the magnetization. No ferromagnetic hypothesis needed. -/
theorem uniformMagnetization_beta_zero
    (d : ℕ) (J h : ℝ) :
    uniformMagnetization d (⟨J, h, 0⟩ : IsingParams ℝ) = 0 :=
  magnetizationInfinite_beta_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h 0

/-- **J-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ 0

/-- **h-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **β-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh 0

/-- **`uniformMagnetization` at `J = 0`**:
`uniformMagnetization d ⟨0, h, β⟩ = tanh(β · h)` (ferromagnetic).

Concrete specialisation of `magnetizationInfinite_J_zero` at site `0`
on the `(latticeGraph d, cubicExhaustion d)` pair. Non-interacting
slice: at `J = 0` the Ising Hamiltonian has no coupling, so each site
is an independent two-state system with Boltzmann weight `exp(β h s)`,
giving `M = tanh(β h)`. -/
theorem uniformMagnetization_J_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    uniformMagnetization d (⟨0, h, β⟩ : IsingParams ℝ) = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf 0

/-- **`uniformMagnetization` at `J = h = 0`**:
`uniformMagnetization d ⟨0, 0, β⟩ = 0`.

At `J = h = 0` the Hamiltonian vanishes identically, so all site-level
correlations are zero. Direct from `correlationInfinite_zero_params_vanish`
at the singleton `{0}`. -/
theorem uniformMagnetization_zero_params
    (d : ℕ) (β : ℝ) :
    uniformMagnetization d (⟨0, 0, β⟩ : IsingParams ℝ) = 0 := by
  unfold uniformMagnetization magnetizationInfinite
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ)} (by simp)

/-- **Z₂ symmetry at `h = 0`**: `uniformMagnetization d ⟨J, 0, β⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_zero_at_h_zero` at
site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. At `h = 0`
the finite-volume Ising model is Z₂-symmetric (flip `σ ↦ −σ`), so
the magnetization vanishes stage-by-stage, hence at ∞-vol. -/
theorem uniformMagnetization_zero_at_h_zero
    (d : ℕ) (J β : ℝ) :
    uniformMagnetization d ⟨J, 0, β⟩ = 0 :=
  magnetizationInfinite_zero_at_h_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β 0

/-- **Right-limit** `uniformMagnetization` → `uniformSpontaneousMagnetization`
as `h → 0⁺`.

Concrete specialization of the abstract
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`
at site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. Realises
the spontaneous magnetization as the right limit of the uniform
(site-independent) magnetization as the external field `h` approaches
zero from above. -/
theorem tendsto_uniformMagnetization_uniformSpontaneousMagnetization_nhdsGT
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (uniformSpontaneousMagnetization d J β)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`uniformSpontaneousMagnetization ≤ uniformMagnetization` at `h > 0`**:
for `0 ≤ J`, `0 < β`, `0 < h`,

`uniformSpontaneousMagnetization d J β
  ≤ uniformMagnetization d ⟨J, h, β⟩`.

Direct specialization of `spontaneousMagnetization_le_magnetizationInfinite`
at site `0` combined with the uniform recasts. The Ising parameter
record `⟨J, h, β⟩` with `0 < h` is ferromagnetic, so the
`uniformMagnetization` bridge applies. -/
theorem uniformSpontaneousMagnetization_le_uniformMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) :
    uniformSpontaneousMagnetization d J β
      ≤ uniformMagnetization d ⟨J, h, β⟩ :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ hh 0

/-! ## Moved: two-point function bounds + symmetry wrappers

The 17 ℤ^d `twoPointFunction_*` / `truncated2TwoPoint_*` /
`truncated3TwoPoint_*` / `truncated4TwoPoint_*` bounds + symmetry
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagTwoPoint`.
The legacy import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
