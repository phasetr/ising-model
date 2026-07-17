import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

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

/-! ## Moved: leeYang subset + slitPlane-locus openness wrappers

The four wrappers
`leeYangSubdomain_subset_slitPlane_locus_latticeGraph`,
`mem_slitPlane_locus_of_mem_leeYangSubdomain_latticeGraph`,
`isOpen_logZ_slitPlane_locus_latticeGraph`, and
`isOpen_slitPlane_locus_h_beta_latticeGraph` now live in
`ComplexRestrictionsLeeYangIsOpen.lean`. -/


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

/-! ## Moved: ℤ^d real-params joint analyticity wrappers

The three wrappers
`real_params_in_analyticity_locus_joint_latticeGraph`,
`real_params_analyticAt_joint_latticeGraph`,
`real_params_image_subset_analyticity_locus_joint_latticeGraph` now
live in `ComplexRestrictionsRealParams.lean`. -/


/-! ## Moved: freeEnergyComplex real-coe regularity wrappers

The three `freeEnergyComplex_{analyticAt,differentiableAt,continuousAt}_h_real_coe_latticeGraph`
wrappers now live in `ComplexRestrictionsFreeEnergyRealCoe.lean`. -/



/-! ## Moved: restrict-real-axis wrappers

The four `{freeEnergy,partitionFunction}Complex_restrict_*_latticeGraph`
real-axis restriction wrappers now live in
`ComplexRestrictionsRestrict.lean`. -/


end Ambient

end IsingModel
