import IsingModel.ComplexAnalyticity.Correlation
import IsingModel.Conditioning.Bounds

/-!
# Trivial second-moment Q-bound for the Cauchy route

For the Cauchy-route bridge `partitionFunctionComplex_norm_ge_of_second_moment_le`
(PR #3048), this module supplies a concrete unconditional `Q`-bound at the
per-fixed-volume level using only the trivial Hamiltonian bound
`|H| ≤ |J|·|E| + |h|·|ι|` (`hamiltonian_abs_le`, `Conditioning/Bounds.lean`).

The resulting `Q := (|J|·|E| + |h|·|ι|)² · Z_ℝ` is volume-dependent (scales with
both `|E|` and `|ι|`) but is **unconditional** — no cluster-expansion assumption.
Combined with the Cauchy-route Q-input bundle constructor (PR #3078) at the
fixed-volume level, this gives an unconditional Cauchy-route hZ provider on a
disc of explicit radius `√2 / (|J|·|E| + |h|·|ι|)`, settling the per-fixed-volume
side of the Lemma 17.5.2 chain unconditionally. Volume-uniformity still requires
either complex cluster-expansion convergence (CE-route Props, Issue #3054 hard
core) or a sharper connected-correlation Q-bound, both research-level.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Trivial pointwise `H²` upper bound** (per-fixed-volume Cauchy input,
Issue #3054 / #3044). At every configuration `σ`,
`H(σ; G, p)² ≤ (|J|·|E| + |h|·|ι|)²`. Immediate from `hamiltonian_abs_le`. -/
theorem hamiltonian_sq_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    hamiltonian G p σ ^ 2 ≤
      (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι) ^ 2 := by
  have h_abs : |hamiltonian G p σ| ≤
      |p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι := hamiltonian_abs_le G p σ
  have h_bound_nn : (0 : ℝ) ≤
      |p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι := by
    have h1 : (0 : ℝ) ≤ |p.J| * G.edgeFinset.card := by positivity
    have h2 : (0 : ℝ) ≤ |p.h| * Fintype.card ι := by positivity
    linarith
  calc hamiltonian G p σ ^ 2
      = |hamiltonian G p σ| ^ 2 := by rw [sq_abs]
    _ ≤ (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h_abs 2

/-- **Trivial second-moment Q-bound** (per-fixed-volume Cauchy input, Issue
#3054 / #3044). Direct upper bound on the Boltzmann-weighted second moment of
the Hamiltonian:
`∑_σ exp(-β.re · H(σ; G, p)) · H(σ; G, p)² ≤ (|J|·|E| + |h|·|ι|)² · Z_ℝ`,
unconditional (no cluster-expansion assumption). The factor scales with both
the edge count `|E|` and the vertex count `|ι|`, so the resulting smallness
radius `|β.im| < √2 / (|J|·|E| + |h|·|ι|)` shrinks with volume; this is the
**per-fixed-volume** Cauchy Q-bound that closes the Cauchy-route Q-input
bundle (PR #3078) unconditionally at each stage. -/
theorem second_moment_bound_trivial
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) (β : ℂ) :
    (∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) *
        hamiltonian G p σ ^ 2)
      ≤ (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι) ^ 2 *
        partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) := by
  classical
  set C : ℝ := (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι) ^ 2 with hC_def
  -- partitionFunction unfolds to ∑_σ Real.exp(-β.re · H(σ; ⟨p.J, p.h, β.re⟩)).
  -- Note: hamiltonian depends only on J and h, not β, so H at p = H at ⟨p.J,p.h,β.re⟩.
  have h_ham_eq : ∀ σ : Config ι,
      hamiltonian G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) σ = hamiltonian G p σ := by
    intro σ; rfl
  have h_pf_eq :
      partitionFunction G (⟨p.J, p.h, β.re⟩ : IsingParams ℝ) =
        ∑ σ : Config ι, Real.exp (-β.re * hamiltonian G p σ) := by
    unfold partitionFunction boltzmannWeight
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [h_ham_eq σ]
  rw [h_pf_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-β.re * hamiltonian G p σ) :=
    (Real.exp_pos _).le
  -- exp(-β.re · H) · H² ≤ exp(-β.re · H) · C  (pointwise bound on H²).
  calc Real.exp (-β.re * hamiltonian G p σ) * hamiltonian G p σ ^ 2
      ≤ Real.exp (-β.re * hamiltonian G p σ) * C :=
        mul_le_mul_of_nonneg_left (hamiltonian_sq_le G p σ) hexp_nn
    _ = C * Real.exp (-β.re * hamiltonian G p σ) := by ring

/-- **Unconditional per-fixed-volume `Z_ℂ` lower bound at `h = 0`** (Issue
#3054 / #3044). Combining `second_moment_bound_trivial` with
`partitionFunctionComplex_norm_ge_of_second_moment_le` (PR #3048) and the
positivity of `partitionFunction`: for any complex `β` with
`β.im² < 2 / (|J|·|E|)²`, the complex partition function at `h = 0` is
non-zero. The smallness radius `|β.im| < √2 / (|J|·|E|)` is volume-dependent;
volume-uniformity requires sharper Q-bounds (cluster expansion). -/
theorem partitionFunctionComplex_ne_zero_of_im_lt_h_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (β : ℂ)
    (hsmall : β.im ^ 2 / 2 *
        ((|J| * G.edgeFinset.card) ^ 2 *
          partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ))
      < partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ)) :
    partitionFunctionComplex G (J : ℂ) 0 β ≠ 0 := by
  have hQ :
      (∑ σ : Config ι, Real.exp (-β.re * hamiltonian G (⟨J, 0, β.re⟩ :
              IsingParams ℝ) σ) *
          hamiltonian G (⟨J, 0, β.re⟩ : IsingParams ℝ) σ ^ 2)
        ≤ (|J| * G.edgeFinset.card) ^ 2 *
          partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ) := by
    have h := second_moment_bound_trivial G (⟨J, 0, β.re⟩ : IsingParams ℝ) β
    simpa using h
  have h_lb :=
    IsingModel.partitionFunctionComplex_norm_ge_of_second_moment_le G
      (⟨J, 0, β.re⟩ : IsingParams ℝ) β hQ
  -- Unfold `(⟨J,0,β.re⟩ : IsingParams ℝ).J = J` and `.h = 0` to match the
  -- `partitionFunctionComplex G (J:ℂ) 0 β` shape in the goal.
  have h_pos : 0 <
      ‖partitionFunctionComplex G
          ((⟨J, 0, β.re⟩ : IsingParams ℝ).J : ℂ)
          ((⟨J, 0, β.re⟩ : IsingParams ℝ).h : ℂ) β‖ := by
    have h_strict : partitionFunction G
        (⟨(⟨J, 0, β.re⟩ : IsingParams ℝ).J,
          (⟨J, 0, β.re⟩ : IsingParams ℝ).h,
          β.re⟩ : IsingParams ℝ) -
        β.im ^ 2 / 2 *
          ((|J| * G.edgeFinset.card) ^ 2 *
            partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ)) > 0 := by
      have hp_eq : (⟨(⟨J, 0, β.re⟩ : IsingParams ℝ).J,
          (⟨J, 0, β.re⟩ : IsingParams ℝ).h, β.re⟩ : IsingParams ℝ) =
          (⟨J, 0, β.re⟩ : IsingParams ℝ) := rfl
      rw [hp_eq]
      linarith
    exact lt_of_lt_of_le h_strict h_lb
  have h_p_eq : ((⟨J, 0, β.re⟩ : IsingParams ℝ).J : ℂ) = (J : ℂ) := rfl
  have h_h_eq : ((⟨J, 0, β.re⟩ : IsingParams ℝ).h : ℂ) = (0 : ℂ) := by
    simp
  rw [h_p_eq, h_h_eq] at h_pos
  exact norm_pos_iff.mp h_pos

/-- **Unconditional per-fixed-volume `Z_ℂ ≠ 0` on a complex closedBall around
`β = 0` at `h = 0`** (Issue #3054 / #3044). Direct quantitative consequence of
`partitionFunctionComplex_ne_zero_of_im_lt_h_zero` combined with the trivial
inequality `|β.im| ≤ ‖β‖ ≤ r`. For `r * (|J|·|E|) < √2`, the complex partition
function at `h = 0` is non-zero on the entire `Metric.closedBall (0:ℂ) r` —
without any cluster-expansion assumption. The radius `√2 / (|J|·|E|)` shrinks
with volume; volume-uniform requires sharper Q-bounds (cluster expansion). -/
theorem partitionFunctionComplex_ne_zero_on_closedBall_h_zero_at_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) {r : ℝ}
    (hr_small : r * (|J| * G.edgeFinset.card) < Real.sqrt 2) :
    ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      partitionFunctionComplex G (J : ℂ) 0 β ≠ 0 := by
  intro β hβ
  rw [Metric.mem_closedBall] at hβ
  -- dist β 0 ≤ r ⇒ ‖β‖ ≤ r ⇒ |β.im| ≤ ‖β‖ ≤ r.
  have h_norm_le : ‖β‖ ≤ r := by
    simpa [dist_zero_right] using hβ
  have h_im_le : |β.im| ≤ r := by
    have h_im_abs_le_norm : |β.im| ≤ ‖β‖ := Complex.abs_im_le_norm β
    linarith
  have hJE_nn : (0 : ℝ) ≤ |J| * G.edgeFinset.card := by positivity
  -- Apply the partitionFunctionComplex_ne_zero_of_im_lt_h_zero predicate.
  apply partitionFunctionComplex_ne_zero_of_im_lt_h_zero G J β
  -- Smallness: β.im² / 2 * ((|J|*|E|)² * Z_ℝ) < Z_ℝ.
  have hZpos : 0 < partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ) :=
    partitionFunction_pos G _
  -- Reduce to β.im² · (|J|·|E|)² < 2.
  -- |β.im| ≤ r and r · (|J|·|E|) < √2; squaring: β.im² ≤ r² ≤ (√2/(|J|·|E|))² = 2/(|J|·|E|)².
  -- More directly: β.im² · (|J|·|E|)² = (|β.im| · (|J|·|E|))² ≤ (r · (|J|·|E|))² < 2.
  by_cases hJE_pos : 0 < |J| * G.edgeFinset.card
  · have h_im_JE_le_r_JE : |β.im| * (|J| * G.edgeFinset.card) ≤
        r * (|J| * G.edgeFinset.card) :=
      mul_le_mul_of_nonneg_right h_im_le hJE_nn
    have h_im_JE_lt_sqrt2 : |β.im| * (|J| * G.edgeFinset.card) < Real.sqrt 2 :=
      lt_of_le_of_lt h_im_JE_le_r_JE hr_small
    have h_im_JE_nn : (0 : ℝ) ≤ |β.im| * (|J| * G.edgeFinset.card) := by positivity
    -- Square both sides.
    have h_sq_lt : (|β.im| * (|J| * G.edgeFinset.card)) ^ 2 < 2 := by
      have : (|β.im| * (|J| * G.edgeFinset.card)) ^ 2 < (Real.sqrt 2) ^ 2 :=
        pow_lt_pow_left₀ h_im_JE_lt_sqrt2 h_im_JE_nn (by norm_num)
      have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by
        rw [sq, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    -- (|β.im|·(|J|·|E|))² = β.im²·(|J|·|E|)².
    have h_rewrite : (|β.im| * (|J| * G.edgeFinset.card)) ^ 2 =
        β.im ^ 2 * (|J| * G.edgeFinset.card) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [h_rewrite] at h_sq_lt
    -- Want β.im²/2 * ((|J|·|E|)² · Z_ℝ) < Z_ℝ.
    -- Equivalent (Z_ℝ > 0) to β.im²/2 * (|J|·|E|)² < 1, i.e., β.im² · (|J|·|E|)² < 2.
    have h_step : β.im ^ 2 / 2 * ((|J| * G.edgeFinset.card) ^ 2 *
        partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ)) =
        (β.im ^ 2 * (|J| * G.edgeFinset.card) ^ 2 / 2) *
          partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ) := by ring
    rw [h_step]
    have h_factor_lt : β.im ^ 2 * (|J| * G.edgeFinset.card) ^ 2 / 2 < 1 := by
      linarith
    have h_lt_one_mul : β.im ^ 2 * (|J| * G.edgeFinset.card) ^ 2 / 2 *
        partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ) <
        1 * partitionFunction G (⟨J, 0, β.re⟩ : IsingParams ℝ) :=
      mul_lt_mul_of_pos_right h_factor_lt hZpos
    linarith
  · -- |J| * |E| = 0, so the (|J|·|E|)² factor is 0 and the LHS is 0 < Z_ℝ trivially.
    have hJE_le_zero : |J| * G.edgeFinset.card ≤ 0 := not_lt.mp hJE_pos
    have hJE_zero : |J| * G.edgeFinset.card = 0 := le_antisymm hJE_le_zero hJE_nn
    rw [hJE_zero]
    simp [hZpos]

end IsingModel
