import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperFerro

/-!
# ℤ^d along-exhaustion ferromagnetic sharper upper bounds at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the ferromagnetic form of the upper
bounds in which each edge contributes `exp (β * J)`: the partition function below
`2 ^ |Λ_n| * exp (β * J * |E_n|)`, its logarithm below `|Λ_n| * log 2 + β * J * |E_n|`, and
the free-energy density below `log 2 + β * J * |E_n| / |Λ_n|`. Every statement here assumes
`0 ≤ J` together with `0 < β`, and the free-energy bound alone also assumes `Λ.volume n`
nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex ferromagnetic Z/logZ/f sharper upper bounds at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic log Z sharper upper bound at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic f sharper upper bound at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

end Ambient
end IsingModel
