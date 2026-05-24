import IsingModel.FieldDerivative.Basic
import IsingModel.Inequalities.GHS.TruncatedDefs

/-!
# Field regularity for correlations and truncated two-point functions

Continuity and differentiability wrappers in the external field parameter.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **correlation ContinuousAt h** (Step 199):
For finite-volume Ising, `correlation G ⟨J, h, β⟩ A` is continuous in h at any h.

Proof: differentiable ⇒ continuous (from `hasDerivAt_correlation_field`). -/
theorem correlation_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    ContinuousAt (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) h :=
  (hasDerivAt_correlation_field G J h β A).continuousAt

/-- **correlation Continuous in h** (Step 199, whole-ℝ). -/
theorem correlation_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    Continuous (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) :=
  continuous_iff_continuousAt.mpr fun h => correlation_continuousAt_field G J h β A

/-- **correlation DifferentiableAt h** (Step 199). -/
theorem correlation_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    DifferentiableAt ℝ (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) h :=
  (hasDerivAt_correlation_field G J h β A).differentiableAt

/-- **correlation Differentiable in h** (Step 199, whole-ℝ). -/
theorem correlation_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    Differentiable ℝ (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) A) :=
  fun h => correlation_differentiableAt_field G J h β A

/-- **truncated2 ContinuousAt h** (Step 200):
For finite-volume Ising, `truncated2 G ⟨J, h, β⟩ i j` is continuous in h at any h.

Proof: `truncated2 = correlation {i,j} - correlation {i} · correlation {j}`,
each continuous in h. -/
theorem truncated2_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    ContinuousAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h := by
  unfold truncated2
  exact (correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))

/-- **truncated2 Continuous in h** (Step 200, whole-ℝ). -/
theorem truncated2_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    Continuous (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) :=
  continuous_iff_continuousAt.mpr fun h => truncated2_continuousAt_field G J h β i j

/-- **truncated2 DifferentiableAt h** (Step 200):
At any h, truncated2 has a derivative via product rule. -/
theorem truncated2_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    DifferentiableAt ℝ (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h := by
  unfold truncated2
  exact (correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))

/-- **truncated2 Differentiable in h** (Step 200, whole-ℝ). -/
theorem truncated2_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    Differentiable ℝ (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) :=
  fun h => truncated2_differentiableAt_field G J h β i j

/-- **truncated2 hasDerivAt in h with explicit value** (Step 242):
For any finite-volume Ising at any `(J, h, β)`, `truncated2 G ⟨J, h, β⟩ i j`
has an h-derivative given by the product rule. This completes the truncated2
explicit-derivative trio (truncated2_hasDerivAt_beta at h = 0, truncated2_hasDerivAt_J
at any h, truncated2_hasDerivAt_field at any J, β). -/
theorem truncated2_hasDerivAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j)
      (deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {i, j}) h -
       (deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {i}) h *
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
        deriv (fun h' => correlation G (⟨J, h', β⟩ : IsingParams ℝ) {j}) h))
      h := by
  unfold truncated2
  have hij := hasDerivAt_correlation_field G J h β {i, j}
  have hi := hasDerivAt_correlation_field G J h β {i}
  have hj := hasDerivAt_correlation_field G J h β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

end IsingModel
