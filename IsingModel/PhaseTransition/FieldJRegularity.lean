import IsingModel.PhaseTransition.BetaRegularity

/-!
# Field and coupling regularity wrappers

This module contains the field- and J-direction regularity wrappers split from
`IsingModel.PhaseTransition`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Magnetization is Continuous in h** (Step 200). -/
theorem magnetization_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    Continuous (fun h' => magnetization G (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_continuous_field G J β _

/-- **Magnetization is Differentiable in h** (Step 200). -/
theorem magnetization_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    Differentiable ℝ (fun h' => magnetization G (⟨J, h', β⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_differentiable_field G J β _

/-- **Susceptibility is ContinuousAt h** (Step 201).
For finite-volume Ising, `susceptibility(i, h) = ∑_j truncated2(i, j, h)` is continuous
in h. Finite-sum continuity + `truncated2_continuousAt_field`. -/
theorem susceptibility_continuousAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    ContinuousAt (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) h := by
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => truncated2_continuousAt_field G J h β i j)

/-- **Susceptibility is Continuous in h** (Step 201, whole-ℝ). -/
theorem susceptibility_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    Continuous (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  continuous_iff_continuousAt.mpr fun h => susceptibility_continuousAt_field G J h β i

/-- **Susceptibility is DifferentiableAt h** (Step 201). -/
theorem susceptibility_differentiableAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    DifferentiableAt ℝ (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) h := by
  have heq_fun : (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) =
      (fun h' => ∑ j : ι, truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) := by
    funext h'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  exact DifferentiableAt.fun_sum (fun j _ =>
    truncated2_differentiableAt_field G J h β i j)

/-- **Susceptibility is Differentiable in h** (Step 201, whole-ℝ). -/
theorem susceptibility_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    Differentiable ℝ (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  fun h => susceptibility_differentiableAt_field G J h β i

/-- **Susceptibility Continuous in J** (Step 208). -/
theorem susceptibility_continuous_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    Continuous (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  have heq_fun : (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i) =
      (fun J' => ∑ j : ι, truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) := by
    funext J'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  exact continuous_finset_sum _ (fun j _ => truncated2_continuous_J G h β i j)

/-- **Magnetization Continuous in J** (Step 208). -/
theorem magnetization_continuous_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    Continuous (fun J' => magnetization G (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_continuous_J G h β _

/-- **Susceptibility Differentiable in J** (Step 211). -/
theorem susceptibility_differentiable_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    Differentiable ℝ (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  have heq_fun : (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i) =
      (fun J' => ∑ j : ι, truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) := by
    funext J'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  exact Differentiable.fun_sum (fun j _ => truncated2_differentiable_J G h β i j)

/-- **Magnetization Differentiable in J** (Step 211). -/
theorem magnetization_differentiable_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i : ι) :
    Differentiable ℝ (fun J' => magnetization G (⟨J', h, β⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_differentiable_J G h β _

/-- **Magnetization HasDerivAt J with explicit value** (Step 215):
For any finite-volume Ising at any `(J, h, β)`,
`d/dJ magnetization(i) = d/dJ ⟨σ_i⟩ = β · Σ_e [⟨σ^{{i}△{u,v}}⟩ - ⟨σ_i⟩·⟨σ^{u,v}⟩]`.
Direct from `hasDerivAt_correlation_J` at `A = {i}`. -/
theorem magnetization_hasDerivAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun J' => magnetization G (⟨J', h, β⟩ : IsingParams ℝ) i)
      (β * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      J := by
  unfold magnetization
  exact hasDerivAt_correlation_J G J h β {i}

/-- **Susceptibility HasDerivAt J with explicit value** (Step 215):
For finite-volume Ising at any `(J, h, β)`, `susceptibility(i, J) = ∑_j truncated2(i, j, J)`
has a J-derivative equal to the sum of J-derivatives of `truncated2`. -/
theorem susceptibility_hasDerivAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i)
      (∑ j : ι, deriv (fun J' => truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) J) J := by
  have heq_fun : (fun J' => susceptibility G (⟨J', h, β⟩ : IsingParams ℝ) i) =
      (fun J' => ∑ j : ι, truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) := by
    funext J'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  apply HasDerivAt.fun_sum
  intro j _
  have h_t := truncated2_hasDerivAt_J G J h β i j
  rw [show deriv (fun J' => truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) J =
      _ from h_t.deriv]
  exact h_t

/-- **Magnetization HasDerivAt h with explicit value**:
For any finite-volume Ising at any `(J, h, β)`,
`d/dh magnetization(i) = d/dh ⟨σ_i⟩ = β · (⟨σ_i · M⟩ - ⟨σ_i⟩ · ⟨M⟩)`.

Direct from `hasDerivAt_correlation_field` at `A = {i}`.

Reference: Glimm–Jaffe §17.6. -/
theorem magnetization_hasDerivAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun h' => magnetization G (⟨J, h', β⟩ : IsingParams ℝ) i)
      (β * (gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
              (fun σ => spinProduct {i} σ * totalMagnetization σ) -
            correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
            gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ) totalMagnetization)) h := by
  unfold magnetization
  exact hasDerivAt_correlation_field G J h β {i}

/-- **Magnetization HasDerivAt β at h = 0 with explicit value**:
For any finite-volume Ising at `h = 0`,
`d/dβ magnetization(i) = d/dβ ⟨σ_i⟩|_{h=0} = J · Σ_e [⟨σ^{{i}△{u,v}}⟩ - ⟨σ_i⟩·⟨σ^{u,v}⟩]`.

Direct from `hasDerivAt_correlation_beta` at `A = {i}`.

Reference: Glimm–Jaffe §17.5. -/
theorem magnetization_hasDerivAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    HasDerivAt (fun β' => magnetization G (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i} *
          correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e)
      β := by
  unfold magnetization
  exact hasDerivAt_correlation_beta G J β {i}

/-- **Susceptibility HasDerivAt h with explicit value**:
For finite-volume Ising at any `(J, h, β)`, `susceptibility(i, h) = ∑_j truncated2(i, j, h)`
has an h-derivative equal to the sum of h-derivatives of `truncated2`.

Direct extension via `truncated2_hasDerivAt_field`.

Reference: Glimm–Jaffe §17.6. -/
theorem susceptibility_hasDerivAt_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i)
      (∑ j : ι, deriv (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h) h := by
  have heq_fun : (fun h' => susceptibility G (⟨J, h', β⟩ : IsingParams ℝ) i) =
      (fun h' => ∑ j : ι, truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) := by
    funext h'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  apply HasDerivAt.fun_sum
  intro j _
  have h_t := truncated2_hasDerivAt_field G J h β i j
  rw [show deriv (fun h' => truncated2 G (⟨J, h', β⟩ : IsingParams ℝ) i j) h =
      _ from h_t.deriv]
  exact h_t


end IsingModel
