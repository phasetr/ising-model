import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

/-!
# Concrete Λ-level Z/f/log Z ratio sandwich and ratio bound wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete Λ-level
`ratio_sandwich` / `ratio_bound` wrappers on `latticeGraph d` at
`h = 0` for `partitionFunctionΛ_latticeGraph`,
`freeEnergyΛ_latticeGraph`, and `log_partitionFunctionΛ_latticeGraph`
(with `J = 0` / `β = 0` / `bundle` variants plus ferromagnetic
counterparts). The 7 `triple_ratio_*` wrappers (sandwich + bound
bundles, J = 0 / β = 0 / ferromagnetic variants) now live in
`HighTemperatureBoundsTripleRatio.lean` (narrowed in PR #1998).
Theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ Z ratio sandwich at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
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
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio sandwich at β=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^
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
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio sandwich bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
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
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio sandwich bundle**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
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
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card)) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ Z ratio upper bound at β=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound at β=0**. -/
theorem
partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

/-- **ℤ^d Λ Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ ferromagnetic Z ratio upper bound bundle**. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) ∧
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) /
        partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ

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
/-! ## Moved: ℤ^d Λ-direct triple-ratio wrappers

The 7 ℤ^d Λ-direct `triple_ratio_sandwich_bundle` and
`triple_ratio_bound_bundle` wrappers (J = 0 / β = 0 trivial slices,
ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsTripleRatio`.
The legacy import path is preserved by re-exporting the new child
from the umbrella module that aggregates both.
-/

end Ambient

end IsingModel
