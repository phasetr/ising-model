import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

/-!
# Concrete continuity / analyticOn wrappers for complex Z / f

Narrow parent module for the residual eleven ℤ^d continuity,
`AnalyticOnNhd` / `AnalyticOn`, and leeYang-related wrappers for
`partitionFunctionComplex` / `freeEnergyComplex` on `latticeGraph d`
(`continuous_*_{h,J,beta,joint}_latticeGraph`,
`partitionFunctionComplex_analyticOnNhd_univ_*`,
`partitionFunctionComplex_{continuousOn,analyticOn}_leeYangDomain_latticeGraph`,
`freeEnergyComplex_{analyticOn,continuousOn,differentiableOn}_leeYangSubdomain_latticeGraph`).
The four `norm_partitionFunctionComplex_le_*` /
`norm_freeEnergyComplex_le_*` bound wrappers were further carved out
into `ComplexContinuityNormNorm.lean` in PR #2160. Theorem names are
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

/-! ## Moved: freeEnergyComplex leeYangSubdomain wrappers

The three `freeEnergyComplex_*_leeYangSubdomain_latticeGraph` wrappers
(`analyticOn`, `continuousOn`, `differentiableOn`) now live in
`ComplexContinuityNormFreeEnergyLeeYang.lean`. -/



/-! ## Moved: Complex norm-bound wrappers

The four wrappers
`norm_partitionFunctionComplex_le_{partitionFunction,trivial_bound,of_re_bound}_latticeGraph`
and `norm_freeEnergyComplex_le_trivial_bound_latticeGraph` now live in
`ComplexContinuityNormNorm.lean`. -/


end Ambient

end IsingModel
