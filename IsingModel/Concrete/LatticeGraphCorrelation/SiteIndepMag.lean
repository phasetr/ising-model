import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition

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

/-! ## Moved: uniformMagnetization bound wrappers

The five `uniformMagnetization_nonneg`, `uniformMagnetization_le_one`,
`neg_one_le_uniformMagnetization`, `abs_uniformMagnetization_le_one`,
`uniformMagnetization_sq_le_one` wrappers now live in
`SiteIndepMagUniformBounds.lean`. -/




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
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d `spontaneousCorrelation`/`spontaneousMagnetization_latticeGraph` wrappers

The 8 ℤ^d wrappers `spontaneousCorrelation_latticeGraph_apply`,
`spontaneousMagnetization_latticeGraph_apply`,
`neg_one_le_spontaneousMagnetization_latticeGraph`,
`abs_spontaneousMagnetization_latticeGraph_le_one`,
`spontaneousMagnetization_latticeGraph_{nonneg,le_one,monotone_J,monotone_beta}`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMagSpontaneous`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: uniformMagnetization trivial-slice + monotonicity wrappers

The seven `uniformMagnetization_*` wrappers
(`{beta_zero,monotone_J,monotone_h,monotone_beta,J_zero,zero_params,zero_at_h_zero}`)
now live in `SiteIndepMagTrivialSlice.lean`. -/


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
The earlier import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
