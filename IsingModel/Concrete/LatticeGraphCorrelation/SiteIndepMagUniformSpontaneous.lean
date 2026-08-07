import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance

/-!
# ℤ^d `uniformSpontaneousMagnetization` wrappers

Narrow child module for ℤ^d `uniformSpontaneousMagnetization*` wrappers
(`_apply`, `_eq_spontaneousMagnetization_any_exhaustion`, `_monotone_J`,
`_monotone_beta`,
`spontaneousMagnetization_latticeGraph_cubicExhaustion_eq_uniform`)
extracted from `SiteIndepMag.lean` in PR #2047. Each is a thin
pass-through to the corresponding `spontaneousMagnetization_*` lemma
at `(latticeGraph d, cubicExhaustion d)`. The bound wrappers (`_nonneg`,
`_le_one`, `neg_one_le_*`, `abs_*_le_one`, `_sq_le_one`) now live in
`SiteIndepMagUniformSpontaneousBounds.lean`. The theorem names are
unchanged from the former `SiteIndepMag` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Unfolding of `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β = spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
theorem uniformSpontaneousMagnetization_apply (d : ℕ) (J β : ℝ) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β 0 := rfl

/-- **`uniformSpontaneousMagnetization` equals `spontaneousMagnetization`
under any Exhaustion** (ferromagnetic): bridges fixed-`cubicExhaustion`
definition to arbitrary Exhaustions via
`spontaneousMagnetization_indep_exhaustion`. -/
theorem uniformSpontaneousMagnetization_eq_spontaneousMagnetization_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β 0 := by
  rw [uniformSpontaneousMagnetization_apply]
  exact spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' hJ hβ 0

/-- **J-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ 0

/-- **β-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ 0

/-- **Bridge**: for `0 ≤ J`, `0 < β`, and any site `i : Fin d → ℤ`,
`spontaneousMagnetization ... J β i = uniformSpontaneousMagnetization d J β`.

Immediate from `spontaneousMagnetization_latticeGraph_cubicExhaustion_eq`
(PR #257). -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_latticeGraph_cubicExhaustion_eq d hJ hβ i 0

/-! ## Moved: uniformSpontaneousMagnetization bound wrappers

The five `uniformSpontaneousMagnetization_*` bound wrappers (`nonneg`,
`le_one`, `neg_one_le`, `abs_le_one`, `sq_le_one`) now live in
`SiteIndepMagUniformSpontaneousBounds.lean`. -/




end Ambient

end IsingModel
