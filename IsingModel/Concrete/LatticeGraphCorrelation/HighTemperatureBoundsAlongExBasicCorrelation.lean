import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

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

/-- **ℤ^d along-exhaustion FV (3.46) at A = ∅ consistency check**:
under `0 ≤ β·J`,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ ∅ n = 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_empty_A
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset (Fin d → ℤ)) n = 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_empty_A
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j} n`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex singleton ferromagnetic vanish**. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i n

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
