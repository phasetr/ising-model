import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatioBoundBundle

/-!
# Concrete §18.3-§18.4 along-ex triple-ratio bound-bundle wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`partitionFunctionAlongExhaustion_*_triple_ratio_bound_bundle*`
wrappers extracted from
`HighTemperatureBoundsAlongExhaustionTripleRatio.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_*_triple_ratio_bound_bundle`
  (direct),
* `*_beta_zero` variant,
* `*_ferromagnetic` variant.

Each result is a thin pass-through of the corresponding ambient
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `HighTemperatureBoundsAlongExhaustionTripleRatio`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d along-ex triple (Z + log Z + f) ratio bound bundle at J=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex triple ratio bound bundle at β=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_bound_bundle_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic triple ratio bound bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    d Λ J β (mul_nonneg hβ.le hJ) n hne

end Ambient

end IsingModel
