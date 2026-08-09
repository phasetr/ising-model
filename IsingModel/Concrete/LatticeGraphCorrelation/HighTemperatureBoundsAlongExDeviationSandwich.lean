import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationFerro

/-!
# ℤ^d along-exhaustion deviation sandwiches for `f_n` and `log Z_n` at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, a sandwich for the deviation of the
free-energy density from `log 2`, between `0` and `β * J * |E_n| / |Λ_n|`, and one for the
deviation of `log Z_n` from `|Λ_n| * log 2`, between `0` and `β * J * |E_n|`. Each appears in
a form assuming `0 ≤ β * J` and in a ferromagnetic form assuming `0 ≤ J` together with
`0 < β`. Nonemptiness of `Λ.volume n` is required by the free-energy statements and by them
alone.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex f deviation sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic f deviation sandwich at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

/-- **ℤ^d along-ex log Z deviation sandwich at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_deviation_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex ferromagnetic log Z deviation sandwich at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_deviation_sandwich_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n) - ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

end Ambient
end IsingModel
