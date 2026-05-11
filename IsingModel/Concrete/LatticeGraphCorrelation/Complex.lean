import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranches
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexSlitPlane
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictions
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntire

/-!
# ℤ^d real/complex analyticity wrappers (fixed-Λ)

Direct ℤ^d forwarders for:

* Real analyticity of `partitionFunctionΛ` / `freeEnergyH` / `freeEnergyJ`
  (using `IsingModel/FreeEnergy.lean`).
* Complex analyticity of `partitionFunctionComplex` / `freeEnergyComplex`
  (GJ §4.6 Thm 4.6.2; using `IsingModel/ComplexAnalyticity.lean` and
  `IsingModel/AmbientComplexAnalyticity.lean`).
* Lee–Yang non-vanishing: `partitionFunctionComplex_nonzero_of_leeYang_*`.
* Slit-plane membership and `freeEnergyComplex` log-branch wrappers.
* `isingEdgePoly` / `leeYangFugacityVec` product expansion.

All theorems are thin pass-throughs of the abstract results in
`ComplexAnalyticity.lean` / `AmbientComplexAnalyticity.lean` applied to the
concrete `Ambient.inducedGraph (IsingModel.latticeGraph d) Λ` at a fixed
finite `Λ : Finset (Fin d → ℤ)`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

/-! ## Moved: per-direction analyticity wrappers (real and complex)

The 12 concrete per-direction `analyticAt` / `analyticOn` wrappers
for `partitionFunction*` / `freeEnergy*` in `h`, `J`, `β` (plus joint
analyticity) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic`.
The legacy import path is preserved by re-importing the new child.
-/



/-! ## Moved: real-complex compatibility / Lee-Yang domain wrappers

The 22 concrete real-complex compatibility, Lee-Yang-domain
non-vanishing, and related restriction wrappers on `latticeGraph d`
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat`.
The legacy import path is preserved by re-importing the new child.
-/


/-! #### Continuity, analyticOn, and norm bounds for complex Z / f

Direct ℤ^d forwarders for continuity, universe / Lee-Yang-domain
`AnalyticOn` restatements, and locally-uniform norm bounds on
`partitionFunctionComplex` / `freeEnergyComplex`. These are the
Montel + Vitali inputs for the infinite-volume completion at ℤ^d. -/


/-! ## Moved: continuity / analyticOn / norm-bound wrappers

The 15 concrete continuity, `AnalyticOnNhd`/`AnalyticOn`, and
norm-bound wrappers for `partitionFunctionComplex` / `freeEnergyComplex`
on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm`.
The legacy import path is preserved by re-importing the new child.
-/


/-! #### Local `log Z` / `freeEnergyComplex` branch on Lee-Yang domain

Direct ℤ^d forwarders for the `exists_logZ_*` / `exists_freeEnergyComplex_*`
local-branch construction, the `partitionFunctionComplex` non-vanishing
on `leeYangSubdomain` / `leeYangDomain`, and the principal-branch
`freeEnergyComplex` `AnalyticOnNhd` on its analyticity locus. These are
the finite-volume GJ §4.6 Thm 4.6.2 branch-form ingredients at ℤ^d. -/

/-! ## Moved: log-branch construction wrappers

The 11 concrete log Z / freeEnergyComplex local-branch construction
wrappers on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranches`.
The legacy import path is preserved by re-importing the new child.
-/


/-! #### slitPlane-locus analyticity + log-branch basepoint evaluation

Direct ℤ^d forwarders for the remaining continuity / differentiable /
analytic-on-slitPlane-locus theorems (h-variable and joint (J, h, β)),
the log-branch basepoint identities, and auxiliary `exists_logZ_*`
ball restatements from `IsingModel/ComplexAnalyticity.lean`. -/

/-! ## Moved: slitPlane-locus + log-branch-on-ball wrappers

The 15 concrete slitPlane-locus continuity / analyticOn / differentiableOn
wrappers and log-branch-on-ball wrappers on `latticeGraph d` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexSlitPlane`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: leeYang inclusions + real-axis restriction wrappers

The 16 concrete leeYangSubdomain ⊆ slitPlane locus inclusions and
real-axis restriction identities now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexRestrictions`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: analyticBranch + entire wrappers

The 12 concrete `leeYangDomain_subset_branch_locus`,
`freeEnergyComplex_exists_analyticBranch*`,
`analyticBranch_freeEnergyComplex_*`,
`continuous_freeEnergyComplex_on_locus`,
`continuousAt/differentiableAt_freeEnergyComplex_at_real_joint`, and
`partitionFunctionComplex_entire_*` wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.ComplexBranchEntire`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **ℤ^d `‖Z_ℂ‖ = Z_ℝ` at real parameters (alias)** (Λ-induced). -/
theorem norm_partitionFunctionComplex_eq_partitionFunction_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_eq_partitionFunction_at_real
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

/-- **ℤ^d edge-term product factorisation** (Λ-induced):
`∏_e exp(β·J·edgeSpin σ e) = exp(β·J·|E|) · ∏_e edgeWeight … (configToFinset σ)`.
Helper for the Friedli-Velenik factorisation of Z_ℂ. -/
theorem prod_exp_beta_J_edgeSpin_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    ∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Complex.exp ((β : ℂ) * (J : ℂ) * IsingModel.edgeSpinComplex σ e)
      = Complex.exp ((β : ℂ) * (J : ℂ) *
            ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              : ℂ))
        * ∏ e ∈
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
              IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2
                (Real.exp (-2 * β * J)) (IsingModel.configToFinset σ) :=
  IsingModel.prod_exp_beta_J_edgeSpin_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J σ

/-- **ℤ^d `isingEdgePoly` evaluated at `configToFinset σ`** (Λ-induced):
product over edges of `edgeWeight`. -/
theorem isingEdgePoly_apply_configToFinset_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)
        (IsingModel.configToFinset σ)
      = ∏ e ∈
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2 t
              (IsingModel.configToFinset σ) :=
  IsingModel.isingEdgePoly_apply_configToFinset
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t σ

/-- **ℤ^d per-configuration Friedli-Velenik factorisation** (Λ-induced):
`exp(-β · H(σ)) = leeYangNormalization · isingEdgePoly · ∏ fugacityVec`. -/
theorem exp_neg_beta_hamiltonian_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h σ)
      = IsingModel.leeYangNormalization (β : ℂ) (J : ℂ) h
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          (Fintype.card (↑Λ : Type _))
        * IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (Real.exp (-2 * β * J)))
            (IsingModel.configToFinset σ)
        * ∏ i ∈ IsingModel.configToFinset σ,
            IsingModel.leeYangFugacityVec (β : ℂ) h i :=
  IsingModel.exp_neg_beta_hamiltonian_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h σ

/-- **ℤ^d `Re(exp(-β · H(σ))) > 0` on Lee-Yang subdomain** (Λ-induced):
per-configuration positive-real-part. Helper for
`partitionFunctionComplex_re_pos_of_leeYangSubdomain`. -/
theorem exp_neg_beta_hamiltonian_re_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < (Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h σ)).re :=
  IsingModel.exp_neg_beta_hamiltonian_re_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ σ

/-- **ℤ^d normalised local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic). Intermediate between
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph` and
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`. -/
theorem exists_normalised_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ}
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, g h₀ = Complex.log
        (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
          (deriv (fun h'' => IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h'' (β : ℂ)) z
            / IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_normalised_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d `Z_ℂ ≠ 0 → Z_ℂ ∈ {z ≠ 0}`** (Λ-induced): non-vanishing
restatement (trivial but useful set-level restatement). -/
theorem partitionFunctionComplex_ne_zero_not_iff_slitPlane_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) (h : ℂ)
    (hne : IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β ≠ 0) :
    IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ ({z : ℂ | z ≠ 0}) :=
  IsingModel.partitionFunctionComplex_ne_zero_not_iff_slitPlane
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h hne

/-- **ℤ^d product-form for `isingEdgePoly` evaluated at `leeYangFugacityVec`**
(Λ-induced): expands `P_E(z(h))` over `Finset ι` subsets. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ) (β h : ℂ) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec β h)
      = ∑ X : Finset (↑Λ : Type _),
          ((IsingModel.graphToEdgeList
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t).map
              fun e => IsingModel.edgeWeight e.1 e.2.1 e.2.2 X).prod *
            ∏ _i ∈ X, IsingModel.leeYangFugacity β h :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t β h

end Ambient

end IsingModel
