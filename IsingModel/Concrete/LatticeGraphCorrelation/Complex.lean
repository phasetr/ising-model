import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexAnalyticityBasic
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexRealCompat
import IsingModel.Concrete.LatticeGraphCorrelation.ComplexContinuityNorm

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

/-- **ℤ^d `Z_ℂ ≠ 0` on `leeYangSubdomain`** (Λ-induced, ferromagnetic). -/
theorem partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

/-- **ℤ^d `Z_ℂ MapsTo ≠ 0` on `leeYangDomain`** (Λ-induced,
ferromagnetic): `Set.MapsTo` restatement of the Lee-Yang
non-vanishing. -/
theorem partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Set.MapsTo (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain {z : ℂ | z ≠ 0} :=
  IsingModel.partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the principal-branch
`slitPlane` analyticity locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergy` analyticity locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): primitive of `Z'/Z`. -/
theorem exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
        (deriv (fun h'' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h'' (β : ℂ)) z
          / IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_logZ_branch_on_ball_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d holomorphic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `exp g = Z` on the ball,
`g h₀ = Complex.log(Z h₀)`. -/
theorem exists_logZ_holomorphic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
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
  IsingModel.exists_logZ_holomorphic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d analytic log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic): `AnalyticOnNhd` refinement. -/
theorem exists_logZ_analytic_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        (∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ))
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ))
      ∧ AnalyticOnNhd ℂ g (Metric.ball h₀ r) :=
  IsingModel.exists_logZ_analytic_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d pointwise analytic `log Z` branch at every `h₀ ∈ leeYangDomain`**
(Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticAt_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g h₀
      ∧ Complex.exp (g h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ g h₀ = Complex.log
          (IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ)) :=
  IsingModel.exists_logZ_analyticAt_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (branch form)** (Λ-induced,
nonempty `Λ`, ferromagnetic): at every `h₀ ∈ leeYangDomain` there is an
`AnalyticAt` representative `f` with `exp(|Λ|·f) = Z` and
`f h₀ = freeEnergyComplex …`. -/
theorem exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ f h₀ = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-- **ℤ^d `freeEnergyComplex` local branch `AnalyticOnNhd ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d `freeEnergyComplex` local branch `DifferentiableOn ball`**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem exists_freeEnergyComplex_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r,
          Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f z)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-! #### slitPlane-locus analyticity + log-branch basepoint evaluation

Direct ℤ^d forwarders for the remaining continuity / differentiable /
analytic-on-slitPlane-locus theorems (h-variable and joint (J, h, β)),
the log-branch basepoint identities, and auxiliary `exists_logZ_*`
ball restatements from `IsingModel/ComplexAnalyticity.lean`. -/

/-- **ℤ^d `Z_ℂ` `ContinuousAt` real `h₀`** (Λ-induced). -/
theorem partitionFunctionComplex_continuousAt_real_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.partitionFunctionComplex_continuousAt_real_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `ContinuousAt` real positive `h₀`** (Λ-induced). -/
theorem freeEnergyComplex_continuousAt_real_pos_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt (fun h : ℂ => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_continuousAt_real_pos_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `AnalyticAt h₀` under `Z h₀ ∈ slitPlane`**
(Λ-induced). -/
theorem analyticAt_freeEnergyComplex_of_slitPlane_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) {h₀ : ℂ}
    (hZ : IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β
        ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.analyticAt_freeEnergyComplex_of_slitPlane_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hZ

/-- **ℤ^d `f_ℂ` `ContinuousOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `DifferentiableOn` slitPlane-locus in `h`**
(Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    DifferentiableOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `AnalyticOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_analyticOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `AnalyticOnNhd` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsOpen {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `ContinuousOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `DifferentiableOn` joint slitPlane-locus** (Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DifferentiableOn ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d log-branch at real basepoint** (Λ-induced):
`Complex.log (Z_ℂ ↑p) = ↑(Real.log (Z_ℝ p))` at real parameters. -/
theorem logZ_branch_at_real_basepoint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    Complex.log (IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = ((Real.log (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p)) : ℂ) :=
  IsingModel.logZ_branch_at_real_basepoint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `exp(|Λ| · f_ℂ) = Z_ℝ` at real parameters** (Λ-induced,
nonempty `Λ`). -/
theorem exp_card_mul_freeEnergyComplex_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    (p : IsingParams ℝ) :
    Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) *
        IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = (IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℂ) :=
  IsingModel.exp_card_mul_freeEnergyComplex_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d log-branch `AnalyticOnNhd ball`** (Λ-induced, ferromagnetic). -/
theorem exists_logZ_analyticOnNhd_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball h₀ r)
      ∧ ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_analyticOnNhd_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `ContinuousOn ball`** (Λ-induced, ferromagnetic). -/
theorem continuous_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, ContinuousOn g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.continuous_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-- **ℤ^d log-branch `DifferentiableOn ball`** (Λ-induced,
ferromagnetic). -/
theorem exists_logZ_differentiableOn_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball h₀ r) ∧
        ∀ z ∈ Metric.ball h₀ r, Complex.exp (g z)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) z (β : ℂ) :=
  IsingModel.exists_logZ_differentiableOn_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hr hsub

/-! #### Lee-Yang subdomain ⊆ slitPlane locus + real-slice inclusions +
function-restriction identities -/

/-- **ℤ^d `leeYangSubdomain ⊆ slitPlane_locus`** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem leeYangSubdomain_subset_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _)))
      ⊆ {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane} :=
  IsingModel.leeYangSubdomain_subset_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `h ∈ leeYangSubdomain ⇒ Z_ℂ ∈ slitPlane`** (Λ-induced). -/
theorem mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.mem_slitPlane_locus_of_mem_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J hh

/-- **ℤ^d `logZ` slitPlane-locus is open** (Λ-induced). -/
theorem isOpen_logZ_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_logZ_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d slitPlane-locus open in `(h, β)`** (Λ-induced). -/
theorem isOpen_slitPlane_locus_h_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℂ) :
    IsOpen {z : ℂ × ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J z.1 z.2
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_slitPlane_locus_h_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J

/-- **ℤ^d real `h₀` (cast) is in `slitPlane_locus`** (Λ-induced). -/
theorem real_coe_mem_slitPlane_locus_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    (h₀ : ℂ) ∈ {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ)
        ∈ Complex.slitPlane} :=
  IsingModel.real_coe_mem_slitPlane_locus_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d real-axis (cast) ⊆ `slitPlane_locus`** (Λ-induced). -/
theorem real_axis_in_slitPlane_locus_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    ((fun h₀ : ℝ => (h₀ : ℂ)) '' Set.univ) ⊆
      {h : ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ)
          ∈ Complex.slitPlane} :=
  IsingModel.real_axis_in_slitPlane_locus_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d real parameter point in joint slitPlane-locus** (Λ-induced). -/
theorem real_params_in_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) ∈
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_in_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d real parameter point `AnalyticAt` jointly** (Λ-induced). -/
theorem real_params_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    AnalyticAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.real_params_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d image of real-parameter cast ⊆ joint slitPlane-locus**
(Λ-induced). -/
theorem real_params_image_subset_analyticity_locus_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)))
        '' Set.univ ⊆
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        z.1 z.2.1 z.2.2 ∈ Complex.slitPlane} :=
  IsingModel.real_params_image_subset_analyticity_locus_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` `AnalyticAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_analyticAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_analyticAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `DifferentiableAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_differentiableAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    DifferentiableAt ℂ
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_differentiableAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` `ContinuousAt` at real `h₀` (cast)** (Λ-induced). -/
theorem freeEnergyComplex_continuousAt_h_real_coe_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (h₀ : ℝ) :
    ContinuousAt
      (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)) (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_continuousAt_h_real_coe
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `f_ℂ` restriction to real axis equals `f_ℝ`** (Λ-induced). -/
theorem freeEnergyComplex_restrict_real_axis_eq_freeEnergy_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_real_axis_eq_freeEnergy
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to real axis equals `↑Z_ℝ`** (Λ-induced). -/
theorem partitionFunctionComplex_restrict_real_axis_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    (fun h : ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) (h : ℂ) (β : ℂ))
      = fun h : ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h, β⟩ : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_real_axis_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` restriction to `IsingParams ℝ`-image = `↑Z_ℝ`**
(Λ-induced). -/
theorem partitionFunctionComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.partitionFunctionComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `f_ℂ` restriction to `IsingParams ℝ`-image = `↑f_ℝ`**
(Λ-induced). -/
theorem freeEnergyComplex_restrict_joint_real_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    (fun p : IsingParams ℝ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ))
      = fun p : IsingParams ℝ => ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ) :=
  IsingModel.freeEnergyComplex_restrict_joint_real_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-! #### Packaged analyticBranch form + Differentiable ℂ entire +
joint real continuity -/

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (symbolic branch-locus form)**
(Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem leeYangDomain_subset_branch_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ) :=
  IsingModel.leeYangDomain_subset_branch_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` has analytic branch over leeYangDomain**
(Λ-induced, nonempty `Λ`, ferromagnetic): headline form. -/
theorem freeEnergyComplex_exists_analyticBranch_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ, AnalyticAt ℂ f h ∧
        Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` analyticBranch (strong form)**
(Λ-induced, nonempty `Λ`, ferromagnetic): additionally identifies the
branch value at the basepoint with the principal-branch
`freeEnergyComplex`. -/
theorem freeEnergyComplex_exists_analyticBranch_strong_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h ∈ IsingModel.leeYangDomain, ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)
      ∧ f h = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ) :=
  IsingModel.freeEnergyComplex_exists_analyticBranch_strong
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (`analyticBranch` packaged form
over `leeYangDomain`)** (Λ-induced, nonempty `Λ`, ferromagnetic). -/
theorem analyticBranch_freeEnergyComplex_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ f : ℂ → ℂ,
          AnalyticAt ℂ f h₀
        ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
            = IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) h₀ (β : ℂ)
        ∧ f h₀ = IsingModel.freeEnergyComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.analyticBranch_freeEnergyComplex_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d packaged `AnalyticOnNhd` on Lee-Yang subdomain** (Λ-induced,
ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `ContinuousOn` joint slitPlane locus (packaged alias)**
(Λ-induced). -/
theorem continuous_freeEnergyComplex_on_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      {z : ℂ × ℂ × ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2
        ∈ Complex.slitPlane} :=
  IsingModel.continuous_freeEnergyComplex_on_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d joint `ContinuousAt` at real parameters** (Λ-induced). -/
theorem continuousAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ContinuousAt
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.continuousAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d joint `DifferentiableAt` at real parameters** (Λ-induced). -/
theorem differentiableAt_freeEnergyComplex_at_real_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      ((p.J : ℂ), (p.h : ℂ), (p.β : ℂ)) :=
  IsingModel.differentiableAt_freeEnergyComplex_at_real_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `Z_ℂ` entire in `h` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Differentiable ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Z_ℂ` entire in `J` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Differentiable ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Z_ℂ` entire in `β` (Differentiable ℂ)** (Λ-induced). -/
theorem partitionFunctionComplex_entire_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Differentiable ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.partitionFunctionComplex_entire_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d `Z_ℂ` jointly entire on ℂ³ (Differentiable ℂ)**
(Λ-induced). -/
theorem partitionFunctionComplex_entire_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Differentiable ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.partitionFunctionComplex_entire_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

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
