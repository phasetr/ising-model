import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuity

/-!
# ℤ^d along-exhaustion free-energy deviation bound and continuity at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the bound
`f_n - log 2 ≤ β * J * |E_n| / |Λ_n|` on the free-energy density, and the bundle bounding by
that same quantity how far `f_n` moves, in absolute value, from its values at `⟨0, 0, β⟩` and
at `⟨J, 0, 0⟩`. Each appears in a form assuming `0 ≤ β * J` and in a ferromagnetic form
assuming `0 ≤ J` together with `0 < β`, and every statement here also needs `Λ.volume n`
nonempty.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex sharper f deviation bound at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic f deviation bound at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

/-- **ℤ^d along-ex f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_continuity_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic f continuity bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_continuity_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    |freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n|
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card ∧
    |freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n|
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_continuity_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

end Ambient
end IsingModel
