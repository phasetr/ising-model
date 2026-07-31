import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# Concrete Complex isingEdgePoly + Hamiltonian + miscellaneous wrappers

Narrow child module for concrete `isingEdgePoly` evaluations,
`exp_neg_beta_hamiltonian_*`, `prod_exp_beta_J_edgeSpin_eq`,
`exists_normalised_logZ_branch_on_ball`,
`partitionFunctionComplex_ne_zero_not_iff_slitPlane`, and
`norm_partitionFunctionComplex_eq_partitionFunction_at_real` wrappers
on `latticeGraph d`. 10 theorems. The theorem names are unchanged from
the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d `‖Z_ℂ‖ = Z_ℝ` at real parameters (alias)** (Λ-induced). -/
theorem norm_partitionFunctionComplex_eq_partitionFunction_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-! #### Friedli-Velenik / Lee-Yang polynomial helpers

Direct ℤ^d forwarders for the remaining Lee-Yang polynomial nonvanishing,
Friedli-Velenik factorisation helpers, `Re(exp(-β·H)) > 0` on the
subdomain, logarithmic branch intermediate step, and non-vanishing
restatement from `IsingModel/ComplexAnalyticity.lean`. Closes ℤ^d
coverage of that module. -/

/-- **ℤ^d Lee-Yang polynomial evaluation is non-zero on the Lee-Yang
domain** (Λ-induced). -/
theorem isingEdgePoly_eval_leeYangFugacityVec_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ IsingModel.leeYangDomain) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ht₀ ht₁ hβ hh

/-- **ℤ^d Lee-Yang normalisation · polynomial is non-zero on the
Lee-Yang domain** (Λ-induced): the Friedli-Velenik RHS factor is
non-zero. -/
theorem leeYangNormalization_mul_isingEdgePoly_eval_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (J : ℂ) {β : ℝ} (hβ : 0 < β) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain)
    (edgeCount siteCount : ℕ) :
    IsingModel.leeYangNormalization (β : ℂ) J h edgeCount siteCount
        * (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
    ht₀ ht₁ J hβ hh edgeCount siteCount

/-! ## Moved: Friedli-Velenik factorisation wrappers

The three factorisation wrappers
`prod_exp_beta_J_edgeSpin_eq_latticeGraph`,
`isingEdgePoly_apply_configToFinset_latticeGraph`, and
`exp_neg_beta_hamiltonian_eq_latticeGraph` now live in
`ComplexIsingPolyFactorization.lean`. -/


/-! ## Moved: Lee-Yang / log-Z / isingEdgePoly tail wrappers

The four wrappers
`exp_neg_beta_hamiltonian_re_pos_latticeGraph`,
`exists_normalised_logZ_branch_on_ball_latticeGraph`,
`partitionFunctionComplex_ne_zero_not_iff_slitPlane_latticeGraph`,
`isingEdgePoly_eval_leeYangFugacityVec_eq_latticeGraph` now live in
`ComplexIsingPolyLeeYangAndLogZ.lean`. -/


end Ambient

end IsingModel
