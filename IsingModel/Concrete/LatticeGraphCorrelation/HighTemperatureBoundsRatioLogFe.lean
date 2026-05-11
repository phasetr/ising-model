import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioBounds

/-!
# ℤ^d Λ-direct log Z + freeEnergy ratio sandwich / bound wrappers at h = 0

Narrow child module for 12 §18.3-§18.4 concrete (`latticeGraph d`)
Λ-direct `log_partitionFunction` and `freeEnergy` ratio_sandwich /
ratio_bound wrappers at h = 0 (with J = 0 / β = 0 trivial slices and
ferromagnetic variants). Theorem names are unchanged from the former
`HighTemperatureBoundsRatioBounds` declarations.
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

/-- **ℤ^d Λ log Z ratio bound bundle**. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic log Z ratio bound bundle**. -/
theorem
log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
        - Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ f ratio bound bundle**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f ratio bound bundle**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card ∧
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ f ratio bound at J=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ f ratio bound at β=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

/-- **ℤ^d Λ ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
