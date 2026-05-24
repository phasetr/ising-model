import IsingModel.AmbientLattice.Defs.Regularity.Defs

/-!
# Lambda-layer regularity split — convergence and susceptibility/magnetization hasDerivAt

Part of the split Lambda-layer regularity wrappers (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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


end Ambient
end IsingModel
