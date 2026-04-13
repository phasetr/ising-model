import IsingModel.Inequalities.GHS

/-!
# Phase transitions: pure and mixed phases

Formalization of concepts from Glimm–Jaffe, §5.1 (pp. 72–74).

## Main results

* `truncated2_le_one` — `0 ≤ ⟨σ_i; σ_j⟩ ≤ 1` for ferromagnetic parameters
* `mixed_phase_truncated2` — the algebraic core of the mixed-phase formula (5.1.5)

## References

* Glimm–Jaffe, *Quantum Physics*, §5.1, pp. 72–74
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Truncated 2-point function bounds

For ferromagnetic parameters, the truncated 2-point function satisfies
`0 ≤ ⟨σ_i; σ_j⟩ ≤ 1` (cf. eq. (5.1.3)).

The lower bound is GKS-II (`truncated2_nonneg` in `GHS.lean`).
The upper bound follows from `⟨σ^A⟩ ≤ 1` and `⟨σ_i⟩ ≥ 0`, `⟨σ_j⟩ ≥ 0`. -/

/-- For ferromagnetic parameters, the truncated 2-point function is at most 1:
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩ ≤ ⟨σ_iσ_j⟩ ≤ 1`. -/
theorem truncated2_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    truncated2 G p i j ≤ 1 := by
  unfold truncated2
  have h1 : correlation G p {i, j} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {i, j})
  have h2 : 0 ≤ correlation G p {i} := gks_first G p hf {i}
  have h3 : 0 ≤ correlation G p {j} := gks_first G p hf {j}
  linarith [mul_nonneg h2 h3]

/-! ## Mixed phase formula (eq. 5.1.5)

For a convex combination `dμ = α dμ₊ + (1-α) dμ₋` of two pure phases
with magnetizations `⟨σ_i⟩₊ = M` and `⟨σ_i⟩₋ = -M`, the mixed-state
magnetization is `⟨σ_i⟩ = M(2α - 1)`.

If the pure phases satisfy the cluster property
`⟨σ_iσ_j⟩₊ → M²` and `⟨σ_iσ_j⟩₋ → M²` as `|i-j| → ∞`,
then `⟨σ_iσ_j⟩ → α M² + (1-α) M² = M²`, so the asymptotic
truncated 2-point function is

`⟨σ_iσ_j⟩_T → M² - M²(2α-1)² = 4α(1-α)M²`.

This vanishes if and only if `α ∈ {0, 1}` (pure phase). -/

/-- **Eq. (5.1.5)** (Glimm–Jaffe, §5.1, p. 73).
The algebraic identity underlying the mixed-phase formula:
`M² - (M(2α-1))² = 4α(1-α)M²`. -/
theorem mixed_phase_truncated2 (M α : ℝ) :
    M ^ 2 - (M * (2 * α - 1)) ^ 2 = 4 * α * (1 - α) * M ^ 2 := by
  ring

/-- The mixed-phase truncated 2-point function vanishes iff the state is pure.
If `0 ≤ α ≤ 1` and `M > 0`, then `4α(1-α)M² = 0` iff `α = 0` or `α = 1`. -/
theorem mixed_phase_pure_iff (M α : ℝ) (hM : M ≠ 0)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    4 * α * (1 - α) * M ^ 2 = 0 ↔ α = 0 ∨ α = 1 := by
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · linarith
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h) hM
  · intro h; rcases h with rfl | rfl <;> simp

end IsingModel
