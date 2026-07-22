import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-direct triple-ratio (Z + log Z + f) sandwich wrappers at h = 0

Narrow child module for 4 §18.3-§18.4 concrete (`latticeGraph d`)
Λ-direct `triple_ratio_sandwich_bundle` wrappers (J = 0 trivial slice,
β = 0 specialisation, ferromagnetic variants). Theorem names are
unchanged from the former
`Concrete/LatticeGraphCorrelation/HighTemperatureBoundsRatioBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d Λ triple (Z + log Z + f) ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ triple ratio sandwich bundle at β=0**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic triple ratio sandwich bundle at β=0**. -/
theorem partitionFunctionΛ_latticeGraph_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    d Λ J β (mul_nonneg hβ.le hJ) hne

/-- **ℤ^d Λ ferromagnetic triple ratio sandwich bundle at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (Real.cosh (β * J) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) /
            partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) /
          partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ))
            - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ))
          - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    d Λ J β (mul_nonneg hβ.le hJ) hne

end Ambient

end IsingModel
