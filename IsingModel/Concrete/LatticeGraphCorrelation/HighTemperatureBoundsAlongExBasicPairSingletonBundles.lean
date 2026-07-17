import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle

/-!
# Concrete §18.3-§18.4 along-ex pair+singleton bundle wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`correlationAlongExhaustion_*_pair_singleton` bundle wrappers
extracted from `HighTemperatureBoundsAlongExhaustionBasic.lean`:

* `correlationAlongExhaustion_*_pair_singleton_bundle_ferromagnetic`,
* `correlationAlongExhaustion_*_pair_singleton_complete_summary`,
* `correlationAlongExhaustion_*_pair_singleton_trivial_slices_bundle`.

Each result is a thin pass-through of the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `HighTemperatureBoundsAlongExhaustionBasic`
declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and
`⟨σ_iσ_j⟩ ≤ 1` at every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j n

/-- **ℤ^d along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex pair + singleton trivial-slices full bundle at
h = 0**: at `J = 0` and `β = 0`, both pair and singleton ℤ^d
along-exhaustion correlations vanish at every stage `n`. ℤ^d wrapper. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (IsingModel.latticeGraph d) Λ J β i j n

end Ambient

end IsingModel
