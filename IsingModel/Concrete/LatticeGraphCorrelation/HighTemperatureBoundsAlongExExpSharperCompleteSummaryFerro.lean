import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerro

/-!
# ℤ^d along-exhaustion ferromagnetic complete-summary bundles at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, ferromagnetic bundles for the partition
function, for its logarithm and for the free-energy density. Each collects a lower bound in
which every edge contributes a factor `cosh (β * J)`, the sharper upper bound in which every
edge contributes `exp (β * J)` instead, and the values taken at `⟨0, 0, β⟩` and at
`⟨J, 0, 0⟩`. Every statement here assumes `0 ≤ J` together with `0 < β`; the free-energy
bundle additionally needs `Λ.volume n` nonempty, which the partition-function and logarithm
bundles do not.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex ferromagnetic Z/logZ/f complete-summary exp bundles at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic log Z complete-summary exp bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n) = ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n) = ((Λ.volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic f complete-summary exp bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

end Ambient

end IsingModel
