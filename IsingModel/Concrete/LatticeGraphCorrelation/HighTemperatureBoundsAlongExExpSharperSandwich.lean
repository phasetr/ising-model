import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich

/-!
# ℤ^d along-exhaustion sharper sandwiches for `Z_n` and `f_n` at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, sandwiches in which the lower bound gives
every edge a factor `cosh (β * J)` and the sharper upper bound gives it `exp (β * J)` instead:
the partition function between `2 ^ |Λ_n| * cosh (β * J) ^ |E_n|` and
`2 ^ |Λ_n| * exp (β * J * |E_n|)`, and the free-energy density between
`log 2 + (|E_n| / |Λ_n|) * log (cosh (β * J))` and `log 2 + β * J * |E_n| / |Λ_n|`. Each
appears under `0 ≤ β * J` and in a ferromagnetic form under `0 ≤ J` together with `0 < β`;
the free-energy statements, and they alone, also need `Λ.volume n` nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex sharper Z high-temp sandwich at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex sharper f high-temp sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_sandwich_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
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
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic Z sharper sandwich at stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
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
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic f sharper sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_sandwich_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
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
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_sandwich_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

end Ambient

end IsingModel
