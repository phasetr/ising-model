import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle

/-!
# Concrete HT AlongExhaustion correlation bound wrappers

Narrow child module for the 8 ℤ^d along-exhaustion correlation
bound wrappers (`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_empty_A`,
`_at_pair_nonneg`, `_at_singleton_ferromagnetic`, `_at_pair_ferromagnetic`,
`_at_singleton_eq_zero_le_one`, `_at_pair_le_one`, `_at_pair_sandwich`,
`_at_pair_singleton_bundle`) extracted from
`HighTemperatureBoundsAlongExhaustionBasic.lean` in PR #2077. Each is
a thin pass-through to the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBoundsAlongExhaustionBasic` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: along-ex correlation simple bound wrappers

The three wrappers
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_empty_A`,
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_nonneg`,
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_ferromagnetic`
now live in
`HighTemperatureBoundsAlongExBasicCorrelationBounds.lean`. -/


/-- **ℤ^d along-ex pair ferromagnetic sandwich at h = 0**: under
`0 ≤ J, 0 < β`, `0 ≤ ⟨σ_i σ_j⟩^Λ_n ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j n

/-- **ℤ^d along-ex singleton sandwich at h = 0**: `= 0 ∧ ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_eq_zero_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex pair correlation ≤ 1 at h = 0**. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one
    (IsingModel.latticeGraph d) Λ J β i j n

/-- **ℤ^d along-ex pair sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex pair+singleton bundle at h = 0**: combines
`{i}`-vanishing with the `{i,j}` sandwich at every stage `n`. ℤ^d
wrapper of `correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ i j n


end Ambient

end IsingModel
