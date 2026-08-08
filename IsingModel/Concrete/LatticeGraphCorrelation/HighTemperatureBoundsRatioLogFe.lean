import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-direct log Z + freeEnergy ratio-sandwich bundles at h = 0

Instantiates the GJ §18.3–§18.4 two-sided zero-field estimates for the Λ-level free energy
and log partition function at `IsingModel.latticeGraph d`, in general and ferromagnetic
form, as single bundled conjunctions.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d Λ f ratio sandwich bundle**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  freeEnergyΛ_high_temp_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f ratio sandwich bundle**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
        Λ.card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
            - freeEnergyΛ (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          - freeEnergyΛ (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
              Λ.card) :=
  freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle
    d Λ J β (mul_nonneg hβ.le hJ) hne

/-- **ℤ^d Λ log Z ratio sandwich bundle**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
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
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic log Z ratio sandwich bundle**. -/
theorem
log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
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
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

end Ambient
end IsingModel
