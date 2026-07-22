import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-induced high-temperature h=0 sandwich / ferromagnetic / bundle wrappers

Narrow child module for four ℤ^d Λ-induced
`correlationΛ_latticeGraph_high_temp_h_zero_*` wrappers extracted from
`HighTemperatureBoundsCorrelationBasic.lean`:

* `_at_pair_sandwich`,
* `_at_singleton_ferromagnetic`,
* `_at_pair_ferromagnetic`,
* `_at_singleton_eq_zero_le_one`.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
