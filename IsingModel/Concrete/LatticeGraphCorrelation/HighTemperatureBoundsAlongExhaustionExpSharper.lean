import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwichLogZ

/-!
# ℤ^d along-exhaustion sharper upper bounds and the `log Z_n` sandwich at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the upper bounds in which each edge
contributes `exp (β * J)`: the partition function below `2 ^ |Λ_n| * exp (β * J * |E_n|)`, its
logarithm below `|Λ_n| * log 2 + β * J * |E_n|`, and the free-energy density below
`log 2 + β * J * |E_n| / |Λ_n|`; together with the sandwich placing `log Z_n` above
`|Λ_n| * log 2 + |E_n| * log (cosh (β * J))` as well. Every statement here assumes
`0 ≤ β * J`, and the free-energy bound alone also assumes `Λ.volume n` nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex sharper Z upper bound at stage `n`**: under `0 ≤ β·J`,
`Z_n ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. ℤ^d wrapper. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex sharper freeEnergy upper bound at stage `n`**: under
`0 < |Λ_n|` and `0 ≤ β·J`, `f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. ℤ^d wrapper. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex sharper log Z upper bound at stage `n`**: under
`0 ≤ β·J`, `log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. ℤ^d wrapper. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex sharper log Z sandwich at stage `n`**: under `0 ≤ β·J`,
`|Λ_n|·log 2 + |E_n|·log cosh(β·J) ≤ log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`.
ℤ^d wrapper. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

end Ambient

end IsingModel
