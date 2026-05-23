import IsingModel.PhaseTransition.CriticalGrowth

/-!
# Beta regularity wrappers

This module contains the beta-direction convergence and regularity wrappers split from
`IsingModel.PhaseTransition`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Correlation length (§17.5)

The correlation length (inverse mass) for the Ising model is defined by
`m(β)⁻¹ = -lim_{|x|→∞} ln⟨σ(0)σ(x)⟩ / |x|`.

For finite volume on a graph G, we define a proxy: the susceptibility
`χ = Σ_j ⟨σ_i; σ_j⟩` serves as a measure of the correlation range.
When `χ → ∞`, the correlation length diverges (critical point).

The monotonicity `χ(β₁) ≤ χ(β₂)` for `β₁ ≤ β₂` follows from:
- `truncated2_nonneg` (each term ≥ 0)
- monotonicity of each `truncated2` in β (from GKS-II + β-monotonicity)

The full correlation length definition and the continuity theorem
(Thm 17.5.1: m(σ) is continuous) require the infinite volume limit
and spectral theory of the transfer matrix. -/

/-! ## Convergence matrix for §5 derived quantities

Named specializations of `correlation_convergent_*` (J/h/β) and
`Tendsto.sub`/`Tendsto.mul`/`tendsto_finset_sum` for the derived
quantities of §5: magnetization (J), truncated 2-point (J/h/β),
and susceptibility (J/h/β).  The lattice (subgraph) versions are
already above.  These complete the "convergence matrix" for the
physically meaningful §5 quantities. -/

/-- **Magnetization J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ Mᵢ(n, h, β)` converges.  Specialization of
`correlation_convergent` at `A = {i}`. -/
theorem magnetization_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => magnetization G ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  correlation_convergent G h hh β hβ {i}

/-- **Truncated 2-point J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(n,h,β)}` converges.

Proof: Each of `⟨σᵢσⱼ⟩`, `⟨σᵢ⟩`, `⟨σⱼ⟩` converges by
`correlation_convergent`; apply `Tendsto.sub` and `Tendsto.mul`. -/
theorem truncated2_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨(n : ℝ), h, β⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent G h hh β hβ {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent G h hh β hβ {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent G h hh β hβ {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Truncated 2-point h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(J,n,β)}` converges. -/
theorem truncated2_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨J, (n : ℝ), β⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_h G J hJ β hβ {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent_h G J hJ β hβ {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent_h G J hJ β hβ {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Truncated 2-point β → ∞ convergence**: for `J ≥ 0`, `h ≥ 0`, the
sequence `n ↦ ⟨σᵢ;σⱼ⟩_{(J,h,n+1)}` converges. -/
theorem truncated2_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i j : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => truncated2 G ⟨J, h, (n + 1 : ℝ)⟩ i j)
      Filter.atTop (nhds L) := by
  obtain ⟨Lij, hij⟩ := correlation_convergent_beta G J hJ h hh {i, j}
  obtain ⟨Li, hLi⟩ := correlation_convergent_beta G J hJ h hh {i}
  obtain ⟨Lj, hLj⟩ := correlation_convergent_beta G J hJ h hh {j}
  refine ⟨Lij - Li * Lj, ?_⟩
  exact hij.sub (hLi.mul hLj)

/-- **Susceptibility J → ∞ convergence**: for `h ≥ 0`, `β > 0`, the
sequence `n ↦ χᵢ(n, h, β)` converges.  Proof: finite sum of convergent
via `tendsto_finset_sum`. -/
theorem susceptibility_convergent_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_J G h hh β hβ i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- **Susceptibility h → ∞ convergence**: for `J ≥ 0`, `β > 0`, the
sequence `n ↦ χᵢ(J, n, β)` converges. -/
theorem susceptibility_convergent_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_h G J hJ β hβ i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- **Susceptibility β → ∞ convergence**: for `J ≥ 0`, `h ≥ 0`, the
sequence `n ↦ χᵢ(J, h, n+1)` converges. -/
theorem susceptibility_convergent_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => susceptibility G ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) := by
  choose Lj hLj using fun j => truncated2_convergent_beta G J hJ h hh i j
  refine ⟨∑ j : ι, Lj j, ?_⟩
  unfold susceptibility
  exact tendsto_finset_sum _ (fun j _ => hLj j)

/-- **Susceptibility is continuous in β at h = 0** (Step 188):
For finite-volume Ising at h = 0, the susceptibility `χ(i, β) = ∑_j truncated2(i, j, β)`
is continuous in β. Finite-sum continuity + `truncated2_continuousAt_beta`. -/
theorem susceptibility_continuousAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    ContinuousAt (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) β := by
  unfold susceptibility
  -- Goal: ContinuousAt (fun β' => ∑ j, truncated2 G ⟨J,0,β'⟩ i j) β
  -- Use tendsto_finset_sum applied to ContinuousAt = Tendsto
  exact tendsto_finset_sum _ (fun j _ => truncated2_continuousAt_beta G J β i j)

/-- **Susceptibility is differentiable in β at h = 0** (Step 191):
For finite-volume Ising at h = 0, `susceptibility(i, β) = ∑_j truncated2(i, j, β)` is
differentiable in β. Each `truncated2` is differentiable (Step 191 helper), and the
finite sum is differentiable. -/
theorem susceptibility_differentiableAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    DifferentiableAt ℝ (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) β := by
  have heq_fun : (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) =
      (fun β' => ∑ j : ι, truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) := by
    funext β'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  -- Each summand differentiable
  exact DifferentiableAt.fun_sum (fun j _ =>
    (truncated2_hasDerivAt_beta G J β i j).differentiableAt)

/-- **Susceptibility is Continuous in β over the whole ℝ at h = 0** (Step 193).
Strengthens `susceptibility_continuousAt_beta` to `Continuous`. -/
theorem susceptibility_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i : ι) :
    Continuous (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) :=
  continuous_iff_continuousAt.mpr fun β => susceptibility_continuousAt_beta G J β i

/-- **Susceptibility is Differentiable in β at h = 0** (Step 193).
Strengthens `susceptibility_differentiableAt_beta` to `Differentiable`. -/
theorem susceptibility_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i : ι) :
    Differentiable ℝ (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) :=
  fun β => susceptibility_differentiableAt_beta G J β i

/-- **Susceptibility HasDerivAt β at h = 0 with explicit derivative** (Step 197):
For finite-volume Ising at h = 0, `susceptibility(i, β) = ∑_j truncated2(i, j, β)` has a
derivative in β equal to the sum of derivatives of `truncated2`. -/
theorem susceptibility_hasDerivAt_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    HasDerivAt (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i)
      (∑ j : ι, deriv (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β) β := by
  have heq_fun : (fun β' => susceptibility G (⟨J, 0, β'⟩ : IsingParams ℝ) i) =
      (fun β' => ∑ j : ι, truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) := by
    funext β'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  apply HasDerivAt.fun_sum
  intro j _
  have h := truncated2_hasDerivAt_beta G J β i j
  -- Need to convert h's specific derivative value to deriv (...) β
  rw [show deriv (fun β' => truncated2 G (⟨J, 0, β'⟩ : IsingParams ℝ) i j) β =
      _ from h.deriv]
  exact h

/-- **Susceptibility HasDerivAt β at general h with explicit derivative** (Step 246):
For finite-volume Ising at any `(J, h, β)`, `susceptibility(i, β) = ∑_j truncated2(i, j, β)`
has a β-derivative equal to the sum of β-derivatives of `truncated2`.

Direct extension of Step 197 from h = 0 to general h via Step 245
(`truncated2_hasDerivAt_beta_general_h`). -/
theorem susceptibility_hasDerivAt_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun β' => susceptibility G (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (∑ j : ι, deriv (fun β' => truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j) β) β := by
  have heq_fun : (fun β' => susceptibility G (⟨J, h, β'⟩ : IsingParams ℝ) i) =
      (fun β' => ∑ j : ι, truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j) := by
    funext β'
    exact susceptibility_apply G _ i
  rw [heq_fun]
  apply HasDerivAt.fun_sum
  intro j _
  have h_t := truncated2_hasDerivAt_beta_general_h G J h β i j
  rw [show deriv (fun β' => truncated2 G (⟨J, h, β'⟩ : IsingParams ℝ) i j) β =
      _ from h_t.deriv]
  exact h_t

/-- **Susceptibility is Continuous in β at general h** (Step 248).
Extends Step 193 from h = 0 to general h via Step 246. -/
theorem susceptibility_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    Continuous (fun β' => susceptibility G (⟨J, h, β'⟩ : IsingParams ℝ) i) :=
  continuous_iff_continuousAt.mpr fun β =>
    (susceptibility_hasDerivAt_beta_general_h G J h β i).continuousAt

/-- **Susceptibility is Differentiable in β at general h** (Step 248). -/
theorem susceptibility_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    Differentiable ℝ (fun β' => susceptibility G (⟨J, h, β'⟩ : IsingParams ℝ) i) :=
  fun β => (susceptibility_hasDerivAt_beta_general_h G J h β i).differentiableAt

/-- **Magnetization is Continuous in β at general h** (Step 248).
Extends Step 198 (h = 0) to general h via Step 244. -/
theorem magnetization_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    Continuous (fun β' => magnetization G (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_continuous_beta_general_h G J h _

/-- **Magnetization is Differentiable in β at general h** (Step 248). -/
theorem magnetization_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i : ι) :
    Differentiable ℝ (fun β' => magnetization G (⟨J, h, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_differentiable_beta_general_h G J h _

/-- **Magnetization is Continuous in β at h = 0** (Step 198).
At h = 0, `magnetization G p i = correlation G p {i}`, which is continuous in β. -/
theorem magnetization_continuous_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i : ι) :
    Continuous (fun β' => magnetization G (⟨J, 0, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_continuous_beta G J _

/-- **Magnetization is Differentiable in β at h = 0** (Step 198). -/
theorem magnetization_differentiable_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (i : ι) :
    Differentiable ℝ (fun β' => magnetization G (⟨J, 0, β'⟩ : IsingParams ℝ) i) := by
  unfold magnetization
  exact correlation_differentiable_beta G J _

/-- **Magnetization β-derivative at general h with explicit value** (Step 244):
For any finite-volume Ising at any `(J, h, β)`, `magnetization(i)` has a β-derivative

  `d/dβ ⟨σ_i⟩ = J · Σ_e [⟨σ^{{i}△e}⟩ - ⟨σ_i⟩·⟨σ^e⟩]`
  `             + h · Σ_j [⟨σ^{{i}△{j}}⟩ - ⟨σ_i⟩·⟨σ_j⟩]`.

Direct application of Step 243 (`hasDerivAt_correlation_beta_general_h`) at `A = {i}`.
Generalises Step 198 (`magnetization_differentiable_beta`) by providing an explicit
derivative value valid at any h. -/
theorem magnetization_hasDerivAt_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (i : ι) :
    HasDerivAt (fun β' => magnetization G (⟨J, h, β'⟩ : IsingParams ℝ) i)
      (J * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {u, v}) -
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
          correlation G (⟨J, h, β⟩ : IsingParams ℝ) {u, v},
        fun u v => by simp [Finset.pair_comm v u]⟩ e
       + h * ∑ j : ι,
          (correlation G (⟨J, h, β⟩ : IsingParams ℝ) (symmDiff {i} {j}) -
           correlation G (⟨J, h, β⟩ : IsingParams ℝ) {i} *
           correlation G (⟨J, h, β⟩ : IsingParams ℝ) {j}))
      β := by
  unfold magnetization
  exact hasDerivAt_correlation_beta_general_h G J h β {i}


end IsingModel
