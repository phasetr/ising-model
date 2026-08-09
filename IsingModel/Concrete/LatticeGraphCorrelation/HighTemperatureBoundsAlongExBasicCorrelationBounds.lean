import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairBase
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic

/-!
# ℤ^d along-exhaustion correlation normalisation and pair nonnegativity

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the normalisation of
`correlationAlongExhaustion` at the empty observable to `1`, and the nonnegativity of the pair
correlation `⟨σ_i σ_j⟩` at that stage. Each is stated under `0 ≤ β * J` and imposes no further
condition on `d`, `Λ`, the sites or the stage.
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

end Ambient
end IsingModel
