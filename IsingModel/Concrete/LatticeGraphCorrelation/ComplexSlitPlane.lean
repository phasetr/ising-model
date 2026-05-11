import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete Complex slitPlane-locus wrappers + log-branch-on-ball wrappers

Narrow child module for concrete slitPlane-locus continuity / analyticOn /
differentiableOn wrappers and the log-branch-on-ball wrappers on
`latticeGraph d`. 15 theorems including
`partitionFunctionComplex_continuousAt_real_h_latticeGraph`,
`freeEnergyComplex_continuousAt_real_pos_h_latticeGraph`,
`analyticAt_freeEnergyComplex_of_slitPlane_h_latticeGraph`,
`freeEnergyComplex_continuousOn/differentiableOn/analyticOn_slitPlane_locus_latticeGraph`,
the joint variants, `logZ_branch_at_real_basepoint_latticeGraph`,
`exp_card_mul_freeEnergyComplex_at_real_latticeGraph`,
`exists_logZ_analyticOnNhd_ball_latticeGraph`,
`continuous_logZ_branch_on_ball_latticeGraph`, and
`exists_logZ_differentiableOn_ball_latticeGraph`. The theorem names
are unchanged from the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient


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


end Ambient

end IsingModel
