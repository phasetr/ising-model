import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio

/-!
# ℤ^d alongExhaustion triple-ratio (Z + log Z + f) sandwich wrappers at h = 0

Narrow child module for the 4 §18.3-§18.4 concrete (`latticeGraph d`)
alongExhaustion `triple_ratio_sandwich_bundle` wrappers (J = 0 trivial
slice, β = 0 specialisation, ferromagnetic variants). Theorem names are
unchanged from the former
`Concrete/LatticeGraphCorrelation/HighTemperatureBoundsAlongExhaustionRatioBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **ℤ^d along-ex triple ratio sandwich bundle at J=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex triple ratio sandwich bundle at β=0, stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic triple ratio sandwich bundle at β=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle_beta_zero
    d Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **ℤ^d along-ex ferromagnetic triple ratio sandwich bundle at J=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  partitionFunctionAlongExhaustion_latticeGraph_h_zero_triple_ratio_sandwich_bundle
    d Λ J β (mul_nonneg hβ.le hJ) n hne

end Ambient

end IsingModel
