import IsingModel.FieldDerivative.CorrelationRegularity
import IsingModel.Inequalities.GHS.Truncated4

/-!
# Field regularity for higher truncated correlations

Continuity and differentiability wrappers for truncated three- and four-point functions.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **truncated3 ContinuousAt h** (Step 202).
truncated3 is a polynomial in correlation values, each continuous in h. -/
theorem truncated3_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k : ι) :
    ContinuousAt (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated3
  exact (((correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))
    |>.add (((continuousAt_const).mul (correlation_continuousAt_field G J h β _)).mul
      (correlation_continuousAt_field G J h β _) |>.mul
      (correlation_continuousAt_field G J h β _))

/-- **truncated3 Continuous in h** (Step 202, whole-ℝ). -/
theorem truncated3_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    Continuous (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) :=
  continuous_iff_continuousAt.mpr fun h => truncated3_continuousAt_field G J h β i j k

/-- **truncated3 DifferentiableAt h** (Step 202). -/
theorem truncated3_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k : ι) :
    DifferentiableAt ℝ (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) h := by
  unfold truncated3
  exact (((correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))
    |>.add (((differentiableAt_const _).mul
      (correlation_differentiableAt_field G J h β _)).mul
      (correlation_differentiableAt_field G J h β _) |>.mul
      (correlation_differentiableAt_field G J h β _))

/-- **truncated3 Differentiable in h** (Step 202, whole-ℝ). -/
theorem truncated3_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    Differentiable ℝ (fun h' => truncated3 G (⟨J, h', β⟩ : IsingParams ℝ) i j k) :=
  fun h => truncated3_differentiableAt_field G J h β i j k

/-- **truncated4 ContinuousAt h** (Step 204).
truncated4 is a polynomial in correlation values, each continuous in h. -/
theorem truncated4_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k l : ι) :
    ContinuousAt (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) h := by
  unfold truncated4
  exact (((correlation_continuousAt_field G J h β _).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))).sub
    ((correlation_continuousAt_field G J h β _).mul (correlation_continuousAt_field G J h β _))

/-- **truncated4 Continuous in h** (Step 204, whole-ℝ). -/
theorem truncated4_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    Continuous (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) :=
  continuous_iff_continuousAt.mpr fun h => truncated4_continuousAt_field G J h β i j k l

/-- **truncated4 DifferentiableAt h** (Step 204). -/
theorem truncated4_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j k l : ι) :
    DifferentiableAt ℝ (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) h := by
  unfold truncated4
  exact (((correlation_differentiableAt_field G J h β _).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))).sub
    ((correlation_differentiableAt_field G J h β _).mul
     (correlation_differentiableAt_field G J h β _))

/-- **truncated4 Differentiable in h** (Step 204, whole-ℝ). -/
theorem truncated4_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    Differentiable ℝ (fun h' => truncated4 G (⟨J, h', β⟩ : IsingParams ℝ) i j k l) :=
  fun h => truncated4_differentiableAt_field G J h β i j k l

end IsingModel
