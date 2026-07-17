import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT pair+singleton bundle wrappers

Narrow child module for the 3 ℤ^d
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_*`
bundle wrappers (`_bundle_ferromagnetic`, `_complete_summary`,
`_trivial_slices_bundle`) extracted from `HighTemperatureBounds.lean`
in PR #2073. Each is a thin pass-through to the corresponding
ambient `correlationΛ_high_temp_h_zero_at_pair_singleton_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩^Λ = 0`, `0 ≤ ⟨σ_iσ_j⟩^Λ`, and
`⟨σ_iσ_j⟩^Λ ≤ 1` into a single triple. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j

/-- **ℤ^d Λ pair + singleton complete-summary bundle at h = 0**: under
`0 ≤ β·J`, packages pair upper bound, pair sandwich lower, singleton
vanishing, and pair vanishing at `J = 0` / `β = 0` trivial slices. ℤ^d
wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 ∧
      0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both pair and singleton ℤ^d Λ-correlations
vanish. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (IsingModel.latticeGraph d) Λ J β i j


end Ambient

end IsingModel
