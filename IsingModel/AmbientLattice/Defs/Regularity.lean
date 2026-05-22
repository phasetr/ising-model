import IsingModel.AmbientLattice.Defs.Correlation

/-!
# Ambient lattice finite-volume regularity wrappers

Susceptibility and parameter-regularity wrappers at the ambient
finite-volume layer.
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

/-- **magnetizationΛ β → ∞ convergence** under ferromagnetic
`J, h ≥ 0`. -/
theorem magnetizationΛ_convergent_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_beta _ J hJ h hh _

/-- **magnetizationΛ h → ∞ convergence** under `J ≥ 0, β > 0`. -/
theorem magnetizationΛ_convergent_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_h _ J hJ β hβ _

/-- **magnetizationΛ J → ∞ convergence** under `h ≥ 0, β > 0`. -/
theorem magnetizationΛ_convergent_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetizationΛ G Λ
        (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_convergent_J _ h hh β hβ _

/-- **susceptibilityΛ β → ∞ convergence** under `J, h ≥ 0`. -/
theorem susceptibilityΛ_convergent_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_beta _ J hJ h hh _

/-- **susceptibilityΛ h → ∞ convergence** under `J ≥ 0, β > 0`. -/
theorem susceptibilityΛ_convergent_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_h _ J hJ β hβ _

/-- **susceptibilityΛ J → ∞ convergence** under `h ≥ 0, β > 0`. -/
theorem susceptibilityΛ_convergent_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibilityΛ G Λ
        (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_convergent_J _ h hh β hβ _

/-- **susceptibilityΛ HasDerivAt β at h = 0** with explicit derivative
as sum over induced-graph sites. -/
theorem susceptibilityΛ_hasDerivAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun β' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β) β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_beta _ J β _

/-- **susceptibilityΛ HasDerivAt β at general h** with explicit
derivative. -/
theorem susceptibilityΛ_hasDerivAt_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => susceptibilityΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun β' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, h, β'⟩ : IsingParams ℝ) i j) β) β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_beta_general_h _ J h β _

/-- **susceptibilityΛ HasDerivAt J** with explicit derivative. -/
theorem susceptibilityΛ_hasDerivAt_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun J' => susceptibilityΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun J' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J', h, β⟩ : IsingParams ℝ) i j) J) J := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_J _ J h β _

/-- **magnetizationΛ HasDerivAt J** with explicit derivative as sum
over induced-graph edges. -/
theorem magnetizationΛ_hasDerivAt_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun J' => magnetizationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) i)
      (β * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_J _ J h β _

/-- **correlationΛ Continuous in β at h = 0**. -/
theorem correlationΛ_continuous_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta _ J A

/-- **correlationΛ Continuous in β at general h**. -/
theorem correlationΛ_continuous_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_beta_general_h _ J h A

/-- **correlationΛ Differentiable in β at h = 0**. -/
theorem correlationΛ_differentiable_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta _ J A

/-- **correlationΛ Differentiable in β at general h**. -/
theorem correlationΛ_differentiable_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun β' => correlationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_beta_general_h _ J h A

/-- **correlationΛ Continuous in `h`**. -/
theorem correlationΛ_continuous_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_field _ J β A

/-- **correlationΛ Differentiable in `h`**. -/
theorem correlationΛ_differentiable_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_field _ J β A

/-- **correlationΛ Continuous in `J`**. -/
theorem correlationΛ_continuous_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Continuous
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuous_J _ h β A

/-- **correlationΛ Differentiable in `J`**. -/
theorem correlationΛ_differentiable_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun J' => correlationΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ) A) := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiable_J _ h β A

/-- **correlationΛ ContinuousAt β at h = 0** at a specific point. -/
theorem correlationΛ_continuousAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun β' => correlationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) A) β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_beta _ J β A

/-- **correlationΛ ContinuousAt h** at a specific point. -/
theorem correlationΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    ContinuousAt
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_continuousAt_field _ J h β A

/-- **correlationΛ DifferentiableAt h** at a specific point. -/
theorem correlationΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    DifferentiableAt ℝ
      (fun h' => correlationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) A) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.correlation_differentiableAt_field _ J h β A

/-- **susceptibilityΛ ContinuousAt β at h = 0**. -/
theorem susceptibilityΛ_continuousAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_beta _ J β _

/-- **susceptibilityΛ DifferentiableAt β at h = 0**. -/
theorem susceptibilityΛ_differentiableAt_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun β' => susceptibilityΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      β := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_beta _ J β _

/-- **susceptibilityΛ ContinuousAt h**. -/
theorem susceptibilityΛ_continuousAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    ContinuousAt
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_continuousAt_field _ J h β _

/-- **susceptibilityΛ DifferentiableAt h**. -/
theorem susceptibilityΛ_differentiableAt_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    DifferentiableAt ℝ
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_differentiableAt_field _ J h β _

/-- **HasDerivAt for `freeEnergyΛ` in β at general h** with explicit
derivative `(|↑Λ|)⁻¹ · ⟨−H⟩`. -/
theorem hasDerivAt_freeEnergyΛ_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => freeEnergyΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => - IsingModel.hamiltonian (inducedGraph G Λ)
                      (⟨J, h, β⟩ : IsingParams ℝ) σ)) β := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_beta_general_h _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in J** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β·∑_e edgeSpin⟩`. -/
theorem hasDerivAt_freeEnergyΛ_J (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun J' => freeEnergyΛ G Λ (⟨J', h, β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
            IsingModel.edgeSpin (K := ℝ) σ e))) J := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_J _ J h β

/-- **HasDerivAt for `freeEnergyΛ` in h** with explicit derivative
`(|↑Λ|)⁻¹ · ⟨β · M⟩` (magnetization per site). -/
theorem hasDerivAt_freeEnergyΛ_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    HasDerivAt (fun h' => freeEnergyΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ))
      ((Fintype.card ↑(Λ : Finset V) : ℝ)⁻¹ *
        IsingModel.gibbsExpectation (inducedGraph G Λ)
          (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * IsingModel.totalMagnetization σ)) h := by
  simp_rw [freeEnergyΛ_apply]
  exact IsingModel.hasDerivAt_freeEnergy_field _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in β** with explicit
derivative as Boltzmann-weighted Hamiltonian sum. -/
theorem hasDerivAt_partitionFunctionΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => partitionFunctionΛ G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        - IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_beta _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in J** with explicit
derivative as Boltzmann-weighted edge-spin sum. -/
theorem hasDerivAt_partitionFunctionΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun J' => partitionFunctionΛ G Λ
        (⟨J', h, β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_J _ J h β

/-- **HasDerivAt for `partitionFunctionΛ` in h** with explicit
derivative as Boltzmann-weighted total-magnetization sum. -/
theorem hasDerivAt_partitionFunctionΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => partitionFunctionΛ G Λ
        (⟨J, h', β⟩ : IsingParams ℝ))
      (∑ σ : IsingModel.Config ↑(Λ : Finset V),
        β * IsingModel.totalMagnetization σ *
          IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h := by
  simp_rw [partitionFunctionΛ_apply]
  exact IsingModel.hasDerivAt_partitionFunction_field _ J h β

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in β** at a
single configuration `σ : Config ↑Λ`. -/
theorem hasDerivAt_boltzmannWeightΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun β' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h, β'⟩ : IsingParams ℝ) σ)
      (- IsingModel.hamiltonian (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) β :=
  IsingModel.hasDerivAt_boltzmannWeight_beta _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in J** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun J' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J', h, β⟩ : IsingParams ℝ) σ)
      (β * (∑ e ∈ (inducedGraph G Λ).edgeFinset,
              IsingModel.edgeSpin (K := ℝ) σ e) *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) J :=
  IsingModel.hasDerivAt_boltzmannWeight_J _ J h β σ

omit [DecidableEq V] in
/-- **HasDerivAt for ambient-induced Boltzmann weight in h** at a
single configuration. -/
theorem hasDerivAt_boltzmannWeightΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (σ : IsingModel.Config ↑(Λ : Finset V)) :
    HasDerivAt
      (fun h' => IsingModel.boltzmannWeight (inducedGraph G Λ)
        (⟨J, h', β⟩ : IsingParams ℝ) σ)
      (β * IsingModel.totalMagnetization σ *
         IsingModel.boltzmannWeight (inducedGraph G Λ)
            (⟨J, h, β⟩ : IsingParams ℝ) σ) h :=
  IsingModel.hasDerivAt_boltzmannWeight_field _ J h β σ

/-- **HasDerivAt for `correlationΛ` in β at h = 0** with explicit
covariance derivative. -/
theorem hasDerivAt_correlationΛ_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun β' => correlationΛ G Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) A)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_beta _ J β A

/-- **HasDerivAt for `correlationΛ` in β at general h** with explicit
covariance derivative. -/
theorem hasDerivAt_correlationΛ_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun β' => correlationΛ G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) A)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e
       + h * ∑ i : ↑(Λ : Finset V),
          (IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {i}) -
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i}))
      β := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_beta_general_h _ J h β A

/-- **HasDerivAt for `correlationΛ` in J** with explicit covariance
derivative. -/
theorem hasDerivAt_correlationΛ_J (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun J' => correlationΛ G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) A)
      (β * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff A {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) A *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_J _ J h β A

/-- **HasDerivAt for `correlationΛ` in h** with explicit covariance
derivative. -/
theorem hasDerivAt_correlationΛ_field (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    HasDerivAt (fun h' => correlationΛ G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) A)
      (β * (IsingModel.gibbsExpectation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => IsingModel.spinProduct A σ *
                          IsingModel.totalMagnetization σ) -
            IsingModel.correlation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) A *
            IsingModel.gibbsExpectation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ)
                IsingModel.totalMagnetization)) h := by
  simp_rw [correlationΛ_apply]
  exact IsingModel.hasDerivAt_correlation_field _ J h β A


/-- **magnetizationΛ HasDerivAt β at general h** with explicit
derivative. -/
theorem magnetizationΛ_hasDerivAt_beta_general_h (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => magnetizationΛ G Λ (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e
       + h * ∑ j : ↑Λ,
          (IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {j}) -
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {i} *
           IsingModel.correlation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ) {j}))
      β := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_beta_general_h _ J h β _

/-- **magnetizationΛ HasDerivAt h** with explicit covariance derivative
on the induced graph. -/
theorem magnetizationΛ_hasDerivAt_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun h' => magnetizationΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      (β * (IsingModel.gibbsExpectation (inducedGraph G Λ)
              (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => IsingModel.spinProduct {i} σ *
                          IsingModel.totalMagnetization σ) -
            IsingModel.correlation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ) {i} *
            IsingModel.gibbsExpectation (inducedGraph G Λ)
                (⟨J, h, β⟩ : IsingParams ℝ)
                IsingModel.totalMagnetization)) h := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_field _ J h β _

/-- **magnetizationΛ HasDerivAt β at h = 0** with explicit derivative
as sum over induced-graph edges. -/
theorem magnetizationΛ_hasDerivAt_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun β' => magnetizationΛ G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ (inducedGraph G Λ).edgeFinset,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {i} *
          IsingModel.correlation (inducedGraph G Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  unfold magnetizationΛ
  simp_rw [correlationΛ_apply]
  exact IsingModel.magnetization_hasDerivAt_beta _ J β _

/-- **susceptibilityΛ HasDerivAt h** with explicit derivative
as sum of `truncated2` h-derivatives over induced-graph sites. -/
theorem susceptibilityΛ_hasDerivAt_field (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) (i : ↑Λ) :
    HasDerivAt
      (fun h' => susceptibilityΛ G Λ (⟨J, h', β⟩ : IsingParams ℝ) i)
      (∑ j : ↑Λ, deriv (fun h' =>
        IsingModel.truncated2 (inducedGraph G Λ)
          (⟨J, h', β⟩ : IsingParams ℝ) i j) h) h := by
  simp_rw [susceptibilityΛ_apply]
  exact IsingModel.susceptibility_hasDerivAt_field _ J h β _


end Ambient

end IsingModel
