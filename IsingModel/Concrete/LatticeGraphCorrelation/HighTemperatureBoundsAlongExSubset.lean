import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedSlices
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants

/-!
# ℤ^d along-exhaustion subset expansion and even-subgraph normalisation (§18.3)

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the subset form of the high-temperature expansion — the partition function at an
arbitrary parameter record as `cosh (β * J) ^ |E_n|` times a sum over edge subsets `X` of
`tanh (β * J) ^ |X|` against the configuration sum of `∏_{e ∈ X} σ_e` weighted by the external
field — together with the statement that the even-subgraph sum `∑_X tanh (β * J) ^ |X|` is at
least `1`, and the value `2 ^ |Λ_n|` taken by the partition function at `⟨0, 0, β⟩` and at
`⟨J, 0, 0⟩`. Only the even-subgraph bound carries a hypothesis, namely `0 ≤ β * J`; the
expansion and the slice values hold with none.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-exhaustion general-h subset expansion (GJ §18.3)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_X tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_subset_form`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_subset_form
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h *
                      ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_subset_form
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d along-exhaustion high-temperature even-subgraph sum is `≥ 1`**:
under `0 ≤ β * J`,
`∑_{X ⊆ E_{Λ_n}, even-degree} tanh(β J)^|X| ≥ 1` at every stage `n`.
ℤ^d wrapper of `one_le_sum_pow_tanh_even_subgraph_alongExhaustion`. -/
theorem one_le_sum_pow_tanh_even_subgraph_alongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_alongExhaustion
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion FV (3.45) at `J = 0` consistency check**:
`Z_n(⟨0, 0, β⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d along-exhaustion FV (3.45) at `β = 0` consistency check**:
`Z_n(⟨J, 0, 0⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
    (IsingModel.latticeGraph d) Λ J n

end Ambient

end IsingModel
