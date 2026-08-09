import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly

/-!
# ℤ^d along-exhaustion free-energy differences against the trivial slices

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the bound `β * J * |E_n| / |Λ_n|` on the difference between the free-energy
density at `⟨J, 0, β⟩` and its value at `⟨0, 0, β⟩`, and on the difference against its value
at `⟨J, 0, 0⟩`. Each difference is bounded under `0 ≤ β * J` and again under the ferromagnetic
pair `0 ≤ J` and `0 < β`, and every statement here also assumes `Λ.volume n` nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex f ratio bound at J=0, stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex f ratio bound at β=0, stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic f ratio bound at J=0, stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

/-- **ℤ^d along-ex ferromagnetic f ratio bound at β=0, stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne


end Ambient
end IsingModel
