import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

/-!
# Concrete correlationΛ pair / singleton high-temperature wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete `correlationΛ_latticeGraph`
basic high-temperature wrappers at `h = 0`: pair nonneg, pair `≤ 1`,
singleton / pair trivial-slice vanishings at `J = 0` and `β = 0`, pair
sandwich, singleton / pair ferromagnetic, singleton `= 0 ∧ ≤ 1`, and the
pair+singleton bundle. Bundle / single-edge-bound / capstone / §18.7
exponential-decay wrappers remain in the parent `HighTemperatureBounds`.
The theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, `0 ≤ correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j}`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ-level pair correlation ≤ 1**:
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j} ≤ 1`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_le_one
    (IsingModel.latticeGraph d) Λ J β i j

/-- **ℤ^d Λ singleton at J=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton_J_zero
    (IsingModel.latticeGraph d) Λ β i

/-- **ℤ^d Λ pair at J=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_J_zero
    (IsingModel.latticeGraph d) Λ β i j

/-- **ℤ^d Λ singleton at β=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton_beta_zero
    (IsingModel.latticeGraph d) Λ J i

/-- **ℤ^d Λ pair at β=0,h=0**: = 0. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_beta_zero
    (IsingModel.latticeGraph d) Λ J i j

/-- **ℤ^d Λ pair sandwich**: `0 ≤ ⟨σ_i σ_j⟩ ≤ 1`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ singleton ferromagnetic vanish**: `⟨σ_i⟩^Λ = 0`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i

/-- **ℤ^d Λ ferromagnetic pair sandwich**: `0 ≤ J, 0 < β` → pair sandwich. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j

/-- **ℤ^d Λ singleton sandwich at h = 0**: `⟨σ_i⟩^Λ = 0 ∧ ≤ 1`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton_eq_zero_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_singleton_eq_zero_le_one
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ pair+singleton bundle at h=0**: combines pair sandwich and
singleton vanishing. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ i j

end Ambient

end IsingModel
