import IsingModel.AmbientLattice.Defs.Regularity.HasDerivBasic

/-!
# Lambda-layer regularity split — hasDerivAt for correlation, magnetization, and susceptibility

Part of the split Lambda-layer regularity wrappers (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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
