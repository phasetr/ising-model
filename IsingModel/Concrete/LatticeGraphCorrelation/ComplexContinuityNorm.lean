import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete continuity / analyticOn / norm-bound wrappers for complex Z / f

Narrow child module for concrete continuity, `AnalyticOnNhd` / `AnalyticOn`,
and norm-bound wrappers for `partitionFunctionComplex` /
`freeEnergyComplex` on `latticeGraph d`. 15 theorems including
`continuous_partitionFunctionComplex_h/J/beta/joint_latticeGraph`,
`partitionFunctionComplex_analyticOnNhd_univ_*`,
`partitionFunctionComplex_continuousOn_leeYangDomain_latticeGraph`,
`freeEnergyComplex_analyticOn/continuousOn/differentiableOn_leeYangSubdomain_latticeGraph`,
and the various `norm_partitionFunctionComplex_le_*` /
`norm_freeEnergyComplex_le_*` bound wrappers. The theorem names are
unchanged from the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `h`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    Continuous (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `J`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℂ) :
    Continuous (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d `Continuous` form of `partitionFunctionComplex` in `β`**
(Λ-induced). -/
theorem continuous_partitionFunctionComplex_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℂ) :
    Continuous (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) :=
  IsingModel.continuous_partitionFunctionComplex_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d joint continuity of `partitionFunctionComplex`** (Λ-induced):
`(J, h, β) : ℂ × ℂ × ℂ ↦ Z_ℂ` is continuous. -/
theorem continuous_partitionFunctionComplex_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Continuous (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) :=
  IsingModel.continuous_partitionFunctionComplex_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOnNhd ℂ Set.univ` in `h`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d joint `AnalyticOnNhd ℂ Set.univ` for `partitionFunctionComplex`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `partitionFunctionComplex` `ContinuousOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_continuousOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_continuousOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_analyticOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergyComplex` `AnalyticOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_analyticOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `ContinuousOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`). -/
theorem freeEnergyComplex_continuousOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_continuousOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `freeEnergyComplex` `DifferentiableOn` on `leeYangSubdomain`**
(Λ-induced, ferromagnetic `β > 0`): Vitali-compatible input. -/
theorem freeEnergyComplex_differentiableOn_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    DifferentiableOn ℂ (fun h' => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h' (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_differentiableOn_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

/-- **ℤ^d `‖Z_ℂ‖ ≤ Z_ℝ(J, Re h, β)`** (Λ-induced): dominate the complex
partition function by its real counterpart at `Re h`. -/
theorem norm_partitionFunctionComplex_le_partitionFunction_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          ⟨J, h.re, β⟩ :=
  IsingModel.norm_partitionFunctionComplex_le_partitionFunction
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d trivial upper bound on `‖Z_ℂ‖`** (Λ-induced):
`‖Z_ℂ‖ ≤ 2^|Λ| · exp(|β|·(|J|·|E|_Λ + |Re h|·|Λ|))`. Locally uniform
on compact sets in `h`; input for Montel in the Vitali lift. -/
theorem norm_partitionFunctionComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + |h.re| * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d `‖Z_ℂ‖` upper bound under `|Re h| ≤ R`** (Λ-induced):
uniform over the strip `|Re h| ≤ R`. -/
theorem norm_partitionFunctionComplex_le_of_re_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) {R : ℝ} {h : ℂ}
    (hh : |h.re| ≤ R) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ Fintype.card (IsingModel.Config (↑Λ : Type _)) *
          Real.exp (|β| *
            (|J| *
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              + R * Fintype.card (↑Λ : Type _))) :=
  IsingModel.norm_partitionFunctionComplex_le_of_re_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J hh

/-- **ℤ^d trivial upper bound on `‖f_ℂ‖`** (Λ-induced, nonempty `Λ`):
`‖f_ℂ‖ ≤ |log ‖Z_ℂ‖|/|Λ| + π/|Λ|`. Combined with `BoundedEdgeDensity`
this gives the Vitali uniform-on-compacts bound. -/
theorem norm_freeEnergyComplex_le_trivial_bound_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] (β J : ℝ) (h : ℂ) :
    ‖IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)‖
      ≤ |Real.log ‖IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ)‖|
          / (Fintype.card (↑Λ : Type _) : ℝ)
        + Real.pi / (Fintype.card (↑Λ : Type _) : ℝ) :=
  IsingModel.norm_freeEnergyComplex_le_trivial_bound
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

end Ambient

end IsingModel
