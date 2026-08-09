import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants

/-!
# ℤ^d high-temperature product expansion of the partition function at zero field

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the
expansion of the partition function as `cosh (β * J) ^ |E|` times the configuration sum of
`∏_e (1 + tanh (β * J) * σ_e)`, on a fixed finite volume `Λ` and at a stage `n` of an
`Ambient.Exhaustion` of `Fin d → ℤ`; together with the value `2 ^ |Λ|` taken at `⟨0, 0, β⟩`
and at `⟨J, 0, 0⟩`, and the normalisation of the correlation at the empty observable to `1`.
Only that normalisation carries a hypothesis, namely `0 ≤ β * J`; the expansions and the slice
values hold with no condition on `J` or `β`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level partition function high-temperature expansion at `h = 0`**:
`Z_Λ(⟨J, 0, β⟩) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionΛ_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d along-exhaustion partition function high-temperature expansion at `h = 0`**:
`Z_n(⟨J, 0, β⟩) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`
at every stage `n`. ℤ^d wrapper of
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d FV (3.45) at `J = 0` consistency check**:
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. ℤ^d wrapper of
`partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d FV (3.45) at `β = 0` consistency check**:
`Z_Λ(⟨J, 0, 0⟩) = 2^|Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d FV (3.46) at `A = ∅` consistency check**:
under `0 ≤ β·J`,
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ ∅ = 1`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_at_empty_A`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset ↑Λ) = 1 :=
  correlationΛ_high_temp_h_zero_at_empty_A
    (IsingModel.latticeGraph d) Λ J β hβJ

end Ambient

end IsingModel
