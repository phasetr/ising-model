import IsingModel.BetaDerivative.Lebowitz

/-!
# Continuity corollaries for beta derivatives

This module contains beta-continuity and differentiability wrappers split from
`IsingModel.BetaDerivative`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Continuity corollaries (Step 120) -/

/-- **Correlation is continuous in β**:
`fun β' => correlation G (⟨J, 0, β'⟩) A` is continuous at `β`.

Proof: differentiable ⇒ continuous (from `hasDerivAt_correlation_beta`).

Reference: GJ §17.5 (implicit); used in Step 120 for pseudoMass composition. -/
theorem correlation_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    ContinuousAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) β :=
  (hasDerivAt_correlation_beta G J β A).continuousAt

/-- **truncated2 is continuous in β at h = 0** (Step 188 helper):
`fun β' => truncated2 G (⟨J, 0, β'⟩) i j` is continuous at β.

At h = 0, `truncated2 = correlation - correlation * correlation`, each continuous in β. -/
theorem truncated2_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    ContinuousAt (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β := by
  unfold truncated2
  exact (correlation_continuousAt_beta G J β _).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))

/-- **truncated2 has a β-derivative at general h** (Step 245):
For any finite-volume Ising at any `(J, h, β)`, `truncated2 G ⟨J, h, β⟩ i j` has a
derivative in β.

`truncated2 = correlation {i,j} - correlation {i} · correlation {j}`. Each correlation has
a β-derivative at general h (`hasDerivAt_correlation_beta_general_h`, Step 243), so the
product rule gives the derivative for truncated2. Generalises Step 191 (h = 0) to any h. -/
theorem truncated2_hasDerivAt_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i j : ι) :
    HasDerivAt (fun β' => truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j)
      (deriv (fun β' => correlation G (⟨J, h, β'⟩ : IsingParams ℝ) {i, j}) β -
       (deriv (fun β' => correlation G (⟨J, h, β'⟩ : IsingParams ℝ) {i}) β *
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
        deriv (fun β' => correlation G (⟨J, h, β'⟩ : IsingParams ℝ) {j}) β))
      β := by
  unfold truncated2
  have hij := hasDerivAt_correlation_beta_general_h G J h β {i, j}
  have hi := hasDerivAt_correlation_beta_general_h G J h β {i}
  have hj := hasDerivAt_correlation_beta_general_h G J h β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

/-- **truncated2 has a β-derivative at h = 0** (Step 191):
For any finite-volume Ising at h = 0, `truncated2 G ⟨J, 0, β⟩ i j` has a derivative in β.

At h = 0, `truncated2 = correlation {i,j} - correlation {i} · correlation {j}`. Each
correlation has a derivative (`hasDerivAt_correlation_beta`), so the product rule gives
the derivative for truncated2. -/
theorem truncated2_hasDerivAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    HasDerivAt (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j)
      (deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {i, j}) β -
       (deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {i}) β *
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {j} +
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i} *
        deriv (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {j}) β))
      β := by
  unfold truncated2
  have hij := hasDerivAt_correlation_beta G J β {i, j}
  have hi := hasDerivAt_correlation_beta G J β {i}
  have hj := hasDerivAt_correlation_beta G J β {j}
  have h_prod := hi.mul hj
  have h_diff := hij.sub h_prod
  -- Convert HasDerivAt's value to use deriv
  rw [hij.deriv, hi.deriv, hj.deriv] at *
  exact h_diff

/-- **correlation is Continuous in β over the whole ℝ at h = 0** (Step 193).
Strengthens `correlation_continuousAt_beta` from `ContinuousAt` to `Continuous`. -/
theorem correlation_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (A : Finset ι) :
    Continuous (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) :=
  continuous_iff_continuousAt.mpr fun β => correlation_continuousAt_beta G J β A

/-- **truncated2 is Continuous in β over the whole ℝ at h = 0** (Step 193).
Strengthens `truncated2_continuousAt_beta` to `Continuous`. -/
theorem truncated2_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j : ι) :
    Continuous (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) :=
  continuous_iff_continuousAt.mpr fun β => truncated2_continuousAt_beta G J β i j

/-- **correlation is Differentiable in β at h = 0** (Step 193).
Strengthens `hasDerivAt_correlation_beta` (single-point) to `Differentiable`. -/
theorem correlation_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (A : Finset ι) :
    Differentiable ℝ (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A) :=
  fun β => (hasDerivAt_correlation_beta G J β A).differentiableAt

/-- **truncated2 is Differentiable in β at h = 0** (Step 193). -/
theorem truncated2_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j : ι) :
    Differentiable ℝ (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) :=
  fun β => (truncated2_hasDerivAt_beta G J β i j).differentiableAt

/-- **correlation is Continuous in β at general h** (Step 247).
Strengthens Step 193 from h = 0 to general h via Step 243's
`hasDerivAt_correlation_beta_general_h`. -/
theorem correlation_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (A : Finset ι) :
    Continuous (fun β' => correlation G (⟨J, h, β'⟩ : IsingParams ℝ) A) :=
  continuous_iff_continuousAt.mpr fun β =>
    (hasDerivAt_correlation_beta_general_h G J h β A).continuousAt

/-- **correlation is Differentiable in β at general h** (Step 247).
Strengthens Step 193 from h = 0 to general h via Step 243. -/
theorem correlation_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (A : Finset ι) :
    Differentiable ℝ (fun β' => correlation G (⟨J, h, β'⟩ : IsingParams ℝ) A) :=
  fun β => (hasDerivAt_correlation_beta_general_h G J h β A).differentiableAt

/-- **truncated2 is Continuous in β at general h** (Step 247). -/
theorem truncated2_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j : ι) :
    Continuous (fun β' => truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j) :=
  continuous_iff_continuousAt.mpr fun β =>
    (truncated2_hasDerivAt_beta_general_h G J h β i j).continuousAt

/-- **truncated2 is Differentiable in β at general h** (Step 247). -/
theorem truncated2_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j : ι) :
    Differentiable ℝ (fun β' => truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j) :=
  fun β => (truncated2_hasDerivAt_beta_general_h G J h β i j).differentiableAt

/-- **truncated3 is ContinuousAt β at h = 0** (Step 203).
truncated3 is a polynomial in correlation values, each continuous in β at h = 0. -/
theorem truncated3_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    ContinuousAt (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) β := by
  unfold truncated3
  exact (((correlation_continuousAt_beta G J β _).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))
    |>.add (((continuousAt_const).mul (correlation_continuousAt_beta G J β _)).mul
      (correlation_continuousAt_beta G J β _) |>.mul
      (correlation_continuousAt_beta G J β _))

/-- **truncated3 Continuous in β at h = 0** (Step 203, whole-ℝ). -/
theorem truncated3_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k : ι) :
    Continuous (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) :=
  continuous_iff_continuousAt.mpr fun β => truncated3_continuousAt_beta G J β i j k

/-- **truncated3 DifferentiableAt β at h = 0** (Step 203). -/
theorem truncated3_differentiableAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k : ι) :
    DifferentiableAt ℝ (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) β := by
  unfold truncated3
  -- Combine 4 differentiable correlation pieces via product rule
  have h1 := (hasDerivAt_correlation_beta G J β {i, j, k}).differentiableAt
  have h2 := ((hasDerivAt_correlation_beta G J β {i}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {j, k}).differentiableAt
  have h3 := ((hasDerivAt_correlation_beta G J β {j}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {i, k}).differentiableAt
  have h4 := ((hasDerivAt_correlation_beta G J β {k}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {i, j}).differentiableAt
  have h5 := (((differentiableAt_const (2 : ℝ)).mul
    (hasDerivAt_correlation_beta G J β {i}).differentiableAt).mul
    (hasDerivAt_correlation_beta G J β {j}).differentiableAt).mul
    (hasDerivAt_correlation_beta G J β {k}).differentiableAt
  exact (((h1.sub h2).sub h3).sub h4).add h5

/-- **truncated3 Differentiable in β at h = 0** (Step 203, whole-ℝ). -/
theorem truncated3_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k : ι) :
    Differentiable ℝ (fun β' => truncated3 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k) :=
  fun β => truncated3_differentiableAt_beta G J β i j k

/-- **truncated4 ContinuousAt β at h = 0** (Step 204).
truncated4 is a polynomial in correlation values, each continuous in β at h = 0. -/
theorem truncated4_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    ContinuousAt (fun β' => truncated4 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k l) β := by
  unfold truncated4
  exact (((correlation_continuousAt_beta G J β _).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))).sub
    ((correlation_continuousAt_beta G J β _).mul (correlation_continuousAt_beta G J β _))

/-- **truncated4 Continuous in β at h = 0** (Step 204, whole-ℝ). -/
theorem truncated4_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k l : ι) :
    Continuous (fun β' => truncated4 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k l) :=
  continuous_iff_continuousAt.mpr fun β => truncated4_continuousAt_beta G J β i j k l

/-- **truncated4 DifferentiableAt β at h = 0** (Step 204). -/
theorem truncated4_differentiableAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j k l : ι) :
    DifferentiableAt ℝ (fun β' => truncated4 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k l) β := by
  unfold truncated4
  have h1 := (hasDerivAt_correlation_beta G J β {i, j, k, l}).differentiableAt
  have h2 := ((hasDerivAt_correlation_beta G J β {i, j}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {k, l}).differentiableAt
  have h3 := ((hasDerivAt_correlation_beta G J β {i, k}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {j, l}).differentiableAt
  have h4 := ((hasDerivAt_correlation_beta G J β {i, l}).differentiableAt).mul
              (hasDerivAt_correlation_beta G J β {j, k}).differentiableAt
  exact ((h1.sub h2).sub h3).sub h4

/-- **truncated4 Differentiable in β at h = 0** (Step 204, whole-ℝ). -/
theorem truncated4_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i j k l : ι) :
    Differentiable ℝ (fun β' => truncated4 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j k l) :=
  fun β => truncated4_differentiableAt_beta G J β i j k l

/-! ## Step 252: truncated3/4 β-direction wrappers at general h -/

/-- **truncated3 Continuous in β at general h** (Step 252).
Extends Step 203 from h = 0 to general h via Step 247. -/
theorem truncated3_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k : ι) :
    Continuous (fun β' => truncated3 G (⟨J, h, β'⟩ : IsingParams ℝ) i j k) := by
  unfold truncated3
  refine (((correlation_continuous_beta_general_h G J h _).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))
    |>.add ?_
  exact ((continuous_const.mul (correlation_continuous_beta_general_h G J h _)).mul
    (correlation_continuous_beta_general_h G J h _)).mul
    (correlation_continuous_beta_general_h G J h _)

/-- **truncated3 Differentiable in β at general h** (Step 252). -/
theorem truncated3_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k : ι) :
    Differentiable ℝ (fun β' => truncated3 G (⟨J, h, β'⟩ : IsingParams ℝ) i j k) := by
  unfold truncated3
  refine (((correlation_differentiable_beta_general_h G J h _).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))
    |>.add ?_
  exact (((differentiable_const (2 : ℝ)).mul
    (correlation_differentiable_beta_general_h G J h _)).mul
    (correlation_differentiable_beta_general_h G J h _)).mul
    (correlation_differentiable_beta_general_h G J h _)

/-- **truncated4 Continuous in β at general h** (Step 252).
Extends Step 204 from h = 0 to general h. -/
theorem truncated4_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k l : ι) :
    Continuous (fun β' => truncated4 G (⟨J, h, β'⟩ : IsingParams ℝ) i j k l) := by
  unfold truncated4
  exact (((correlation_continuous_beta_general_h G J h _).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))).sub
    ((correlation_continuous_beta_general_h G J h _).mul
     (correlation_continuous_beta_general_h G J h _))

/-- **truncated4 Differentiable in β at general h** (Step 252). -/
theorem truncated4_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k l : ι) :
    Differentiable ℝ (fun β' => truncated4 G (⟨J, h, β'⟩ : IsingParams ℝ) i j k l) := by
  unfold truncated4
  exact (((correlation_differentiable_beta_general_h G J h _).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))).sub
    ((correlation_differentiable_beta_general_h G J h _).mul
     (correlation_differentiable_beta_general_h G J h _))

end IsingModel
