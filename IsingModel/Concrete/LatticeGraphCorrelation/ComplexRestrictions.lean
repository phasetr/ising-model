import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete Complex leeYang inclusions + real-axis restriction wrappers

Narrow child module for concrete leeYangSubdomain ⊆ slitPlane locus
inclusions, real-axis restriction identities, and `_h_real_coe` /
`_restrict_real_axis_eq_*` / `_restrict_joint_real_eq_*` wrappers on
`latticeGraph d`. 16 theorems including
`leeYangSubdomain_subset_slitPlane_locus_latticeGraph`,
`mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph`,
`isOpen_logZ_slitPlane_locus_latticeGraph`,
`isOpen_slitPlane_locus_h_beta_latticeGraph`,
`real_coe_mem_slitPlane_locus_h_latticeGraph`,
`real_axis_in_slitPlane_locus_h_latticeGraph`,
`real_params_in_analyticity_locus_joint_latticeGraph`,
`real_params_analyticAt_joint_latticeGraph`,
`real_params_image_subset_analyticity_locus_joint_latticeGraph`,
`freeEnergyComplex_analyticAt/differentiableAt/continuousAt_h_real_coe_latticeGraph`,
`freeEnergyComplex_restrict_real_axis_eq_freeEnergy_latticeGraph`,
`partitionFunctionComplex_restrict_real_axis_eq_latticeGraph`,
`partitionFunctionComplex_restrict_joint_real_eq_latticeGraph`, and
`freeEnergyComplex_restrict_joint_real_eq_latticeGraph`. The theorem
names are unchanged from the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient

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


end Ambient

end IsingModel
