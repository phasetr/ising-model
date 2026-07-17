import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerroBundle
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerroZ

/-!
# Concrete alongExhaustion strict-deviation bundle + residual ferromagnetic wrappers at h = 0

Narrow child module for the remaining ℤ^d alongExhaustion strict
deviation wrappers at `h = 0`: the
`partitionFunctionAlongExhaustion_*_strict_deviation_bundle` pair
(general and ferromagnetic), plus the two residual ferromagnetic
strict-deviation wrappers
`partitionFunctionAlongExhaustion_*_pow_two_lt_ferromagnetic` and
`log_partitionFunctionAlongExhaustion_*_deviation_pos_ferromagnetic`.
Each wrapper is a thin pass-through to the corresponding ambient lemma
at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-- **ℤ^d along-ex Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_strict_deviation_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n hne hEpos

/-- **ℤ^d along-ex ferromagnetic Z + log Z + f strict deviation bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_strict_deviation_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
        < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    0 < Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    0 < freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_strict_deviation_bundle
    d Λ J β (mul_pos hβ hJ) n hne hEpos

/-- **ℤ^d along-ex ferromagnetic Z strict deviation at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    (2 : ℝ) ^ (Λ.volume n).card
      < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hEpos

/-- **ℤ^d along-ex ferromagnetic log Z strict deviation at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_deviation_pos_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    0 < Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hEpos

end Ambient
end IsingModel
