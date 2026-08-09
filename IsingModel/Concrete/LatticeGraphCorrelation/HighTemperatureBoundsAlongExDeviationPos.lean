import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro

/-!
# ℤ^d along-exhaustion strict deviation from the free-spin values at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, strict versions of the deviation bounds:
the free-energy density exceeds `log 2`, the partition function exceeds `2 ^ |Λ_n|`, and its
logarithm exceeds `|Λ_n| * log 2`. Every statement here requires the stage-`n` induced
subgraph to carry at least one edge; the free-energy statements additionally require
`Λ.volume n` nonempty, which the partition-function and logarithm statements do not. The sign
condition is `0 < β * J`, sharpened in the ferromagnetic free-energy form to `0 < J` together
with `0 < β`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-- **ℤ^d along-ex f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos
    (IsingModel.latticeGraph d) Λ J β hβJ n hne hEpos

/-- **ℤ^d along-ex ferromagnetic f strict deviation at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_pos_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne hEpos

/-- **ℤ^d along-ex Z strict deviation at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_pow_two_lt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt
    (IsingModel.latticeGraph d) Λ J β hβJ n hEpos

/-- **ℤ^d along-ex log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_deviation_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos
    (IsingModel.latticeGraph d) Λ J β hβJ n hEpos

end Ambient
end IsingModel
