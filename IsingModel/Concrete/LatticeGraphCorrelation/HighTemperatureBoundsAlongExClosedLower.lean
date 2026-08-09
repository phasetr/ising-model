import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosed

/-!
# ℤ^d along-exhaustion high-temperature closed form and lower bounds at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the high-temperature representation of
the partition function as `2 ^ |Λ_n| * cosh (β * J) ^ |E_n|` times the even-subgraph sum
`∑_X tanh (β * J) ^ |X|`, together with the lower bounds recorded alongside it: nonnegativity
of the correlation at an arbitrary observable, the partition function above
`2 ^ |Λ_n| * cosh (β * J) ^ |E_n|`, and the free-energy density above
`log 2 + (|E_n| / |Λ_n|) * log (cosh (β * J))`. The representation itself carries no
hypothesis; each bound assumes `0 ≤ β * J`, and the free-energy bound additionally needs
`Λ.volume n` nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-exhaustion partition function high-temperature closed form (FV §3.7.3 eq. (3.45))**:
at every stage `n`,
`partitionFunctionAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  = 2^|Λ_n| · cosh(βJ)^|E_{Λ_n}| · ∑_{X ⊆ E_{Λ_n}, even-degree} tanh(βJ)^|X|`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑(Λ.volume n),
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-exhaustion correlation nonnegativity from FV (3.46)**:
under `0 ≤ β * J`,
`0 ≤ correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ A n`
at every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_nonneg`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_high_temp_h_zero_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ A n

/-- **ℤ^d along-exhaustion partition function high-temperature lower bound (FV (3.45))**:
under `0 ≤ β * J`, at every stage `n`,
`partitionFunctionAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  ≥ 2^|Λ_n| · (cosh(βJ))^|E_{Λ_n}|`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_lower_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion free-energy high-temperature lower bound from FV (3.45)**:
under `0 ≤ β * J` and `0 < |Λ_n|`, at stage `n`,
`freeEnergyAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  ≥ log 2 + (|E_{Λ_n}|/|Λ_n|) · log(cosh(β·J))`.
ℤ^d wrapper of `freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_lower_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

end Ambient

end IsingModel
