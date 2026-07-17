import IsingModel.AmbientLattice.Defs.Core

/-!
# Lambda-layer regularity split — susceptibility definition and free-energy/magnetization regularity

Part of the split Lambda-layer regularity wrappers (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- The **susceptibility** on a finite volume `Λ` at site `i : ↑Λ`:
`χ_Λ(i) = Σ_{j : ↑Λ} ⟨σ_i; σ_j⟩ = IsingModel.susceptibility (inducedGraph G Λ) p i`.
Direct analog of `IsingModel.susceptibility` at the ambient-lattice Λ layer,
matching the `correlationΛ` / `magnetizationΛ` / `partitionFunctionΛ` pattern.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
noncomputable def susceptibilityΛ (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (i : ↑Λ) : ℝ :=
  IsingModel.susceptibility (inducedGraph G Λ) p i

/-- **Unfolding of `susceptibilityΛ`**:
`susceptibilityΛ G Λ p i = IsingModel.susceptibility (inducedGraph G Λ) p i`,
by definition. -/
theorem susceptibilityΛ_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) (i : ↑Λ) :
    susceptibilityΛ G Λ p i = IsingModel.susceptibility (inducedGraph G Λ) p i :=
  rfl

/-- **`susceptibilityΛ ≥ 0`** for ferromagnetic `p` at any site `i : ↑Λ`.
Direct lift of `IsingModel.susceptibility_nonneg` through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)`. -/
theorem susceptibilityΛ_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ susceptibilityΛ G Λ p i :=
  IsingModel.susceptibility_nonneg (inducedGraph G Λ) p hf i

/-! ## Step 258: Λ-layer regularity wrappers (β/h/J at general h) -/

/-- **freeEnergyΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Continuous (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_beta_general_h _ J h

/-- **freeEnergyΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_beta_general_h _ J h

/-- **freeEnergyΛ Continuous in h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Continuous (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_field _ J β

/-- **freeEnergyΛ Differentiable in h** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_field _ J β

/-- **freeEnergyΛ Continuous in J** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    Continuous (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_continuous_J _ h β

/-- **freeEnergyΛ Differentiable in J** (Step 258, general G, Λ). -/
theorem freeEnergyΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) :
    Differentiable ℝ (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ)) :=
  IsingModel.freeEnergy_differentiable_J _ h β

/-- **magnetizationΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem magnetizationΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Continuous (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta_general_h _ J h _

/-- **magnetizationΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem magnetizationΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta_general_h _ J h _

/-- **magnetizationΛ Continuous in `h`**. -/
theorem magnetizationΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_continuous_field _ J β _

/-- **magnetizationΛ Differentiable in `h`**. -/
theorem magnetizationΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ)
    (i : ↑Λ) :
    Differentiable ℝ
      (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_differentiable_field _ J β _

/-- **magnetizationΛ Continuous in `J`**. -/
theorem magnetizationΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_continuous_J _ h β _

/-- **magnetizationΛ Differentiable in `J`**. -/
theorem magnetizationΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ
      (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_differentiable_J _ h β _

/-- **susceptibilityΛ Continuous in β at general h** (Step 258, general G, Λ). -/
theorem susceptibilityΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Continuous (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_beta_general_h _ J h _

/-- **susceptibilityΛ Differentiable in β at general h** (Step 258, general G, Λ). -/
theorem susceptibilityΛ_differentiable_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_beta_general_h _ J h _

/-- **susceptibilityΛ Continuous in `h`**. -/
theorem susceptibilityΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_field _ J β _

/-- **susceptibilityΛ Differentiable in `h`**. -/
theorem susceptibilityΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ)
    (i : ↑Λ) :
    Differentiable ℝ
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_field _ J β _

/-- **susceptibilityΛ Continuous in `J`**. -/
theorem susceptibilityΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuous_J _ h β _

/-- **susceptibilityΛ Differentiable in `J`**. -/
theorem susceptibilityΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ
      (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiable_J _ h β _


end Ambient
end IsingModel
