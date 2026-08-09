import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariantsGeneralH

/-!
# ℤ^d high-temperature expansion of the partition function at a general field (§18.3)

Instantiates at `IsingModel.latticeGraph d`, at an arbitrary parameter record, the expansion
of the partition function as `cosh (β * J) ^ |E|` times the configuration sum of
`∏_e (1 + tanh (β * J) * σ_e)` weighted by `exp (β * h * ∑_i σ_i)`, on a fixed finite volume
`Λ` and at a stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`; the same expansion
reorganised as a sum over edge subsets `X` of `tanh (β * J) ^ |X|` against the configuration
sum of `∏_{e ∈ X} σ_e` with that same field weight; and, at zero external field, the closed
form `2 ^ |Λ| * cosh (β * J) ^ |E_Λ|` times the even-subgraph sum. No statement here imposes
a condition on the parameter record.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ-level partition function high-temperature expansion (general h)**:
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑_i σ_i)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        (∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) :=
  partitionFunctionΛ_high_temp_expansion (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d along-exhaustion partition function high-temperature expansion (general h)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j) · exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        (∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h *
                  ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) :=
  partitionFunctionAlongExhaustion_high_temp_expansion
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d high-temperature partition function closed form (FV §3.7.3 eq. (3.45))**:
on the ℤ^d induced subgraph at zero external field,
`Z_Λ(⟨J, 0, β⟩) = 2^|Λ| · (cosh(β J))^|E_Λ| · ∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X|`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d general-h subset expansion (GJ §18.3)**:
on the ℤ^d induced subgraph,
`Z_Λ(p) = (cosh βJ)^|E_Λ| · ∑_X tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_subset_form`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_subset_form
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑Λ,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ↑Λ, Spin.sign ℝ (σ i)) :=
  partitionFunctionΛ_high_temp_expansion_subset_form
    (IsingModel.latticeGraph d) Λ p

end Ambient
end IsingModel
