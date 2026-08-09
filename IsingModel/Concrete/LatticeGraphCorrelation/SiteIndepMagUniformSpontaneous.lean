import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance

/-!
# The ℤ^d uniform spontaneous magnetization

Concrete statements about `uniformSpontaneousMagnetization`, the value of
`spontaneousMagnetization` at `IsingModel.latticeGraph d` along
`Ambient.cubicExhaustion d` taken at the origin. That unfolding holds by definition and
takes no hypothesis.

The exhaustion bridge and the site-independence statement each assume a non-negative
coupling and a positive inverse temperature: under those the uniform value agrees with the
spontaneous magnetization at the origin computed along any other `Ambient.Exhaustion` of
`Fin d → ℤ`, and the spontaneous magnetization along the cubic exhaustion has that same
value at every site.

The monotonicity statements assume less, each dropping the condition on the parameter it
varies: monotone in the coupling on `Set.Ici 0` under a positive inverse temperature alone,
and monotone in the inverse temperature on `Set.Ioi 0` under a non-negative coupling alone.
No instance argument is taken.
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

end Ambient

end IsingModel
