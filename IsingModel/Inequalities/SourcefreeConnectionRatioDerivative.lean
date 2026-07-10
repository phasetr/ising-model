import IsingModel.Inequalities.SourcefreeConnectionUnconditional
import IsingModel.Inequalities.SourcefreeConnectionCurrentDeriv
import IsingModel.BetaDerivative.Monotonicity
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Random-current ratio-derivative identity (Stage D)

This file assembles **Stage D** of the random-current build toward the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue #4386, thread
#4418): the closed *ratio-derivative identity*
\[
  \partial_\beta\log\langle\sigma_x\sigma_y\rangle_\Lambda
    = \frac{1}{2\beta}\Big(\mathbb{E}^{x\leftrightarrow y}\lvert M\rvert
        - \mathbb{E}\,\lvert M\rvert\Big),
\]
where `|M| = Current.total M`, the both-sourcefree summand is
`D_β(M) = Current.doubledSourcefreeSummand`, and the `D`-normalised expectations
of the total-current observable are
`E^{x↔y}|M| = (∑'_{x↔y} |M| D) / (∑'_{x↔y} D)` and
`E|M| = (∑'_M |M| D) / (∑'_M D)`.

It takes the already-merged pieces:
* the sourcefree connection representation of the *square*
  `⟨σσ⟩² = (∑'_{x↔y} D)/(∑'_M D)`
  (`Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond`), and
* the per-current derivative identity C3′
  `∂_β D_β(M) = (|M|/β) D_β(M)`
  (`Current.hasDerivAt_doubledSourcefreeSummand_beta`),

and differentiates under the `∑'` on a fixed finite volume `Λ` (no
volume-uniformity wall: `Λ` is fixed/finite, `E` finite, and the `∑'` runs over
`Current G Λ = E → ℕ` with factorial decay).

## Main results

* `Current.weight_eq_pow_total_mul_weight_one` (F1) — `w_β(n) = β^{|n|} w_1(n)`.
* `Current.doubledSourcefreeSummand_eq_pow_total_mul` (F2) —
  `D_β(M) = β^{|M|} D_1(M)`.
* `Current.doubledSourcefree_mono_beta` (F3) — monotone in `β` on `[0,·]`.
* `Current.total_mul_doubledSourcefree_le` (M1) — `|M| D_β(M) ≤ D_{2β}(M)`.
* `Current.summable_total_mul_doubledSourcefree` (M2) — `Summable (|M| D_β(M))`.
* `Current.hasDerivAt_tsum_doubledSourcefree_beta` (D1) — the `β`-derivative of
  the total mass `∑'_M D_β(M)`.
* `Current.hasDerivAt_tsum_reachable_doubledSourcefree_beta` (D2) — the
  `β`-derivative of the connected mass `∑'_{x↔y} D_β(M)`.
* `Current.hasDerivAt_log_correlation_beta` (capstone) — the ratio-derivative
  identity.

This brick supplies **only** the exact ratio-derivative identity; it does *not*
bound the excess `E^{x↔y}|M| − E|M|` (the genuine OZ backbone-length estimate,
`hLogLip`, is a later multi-session brick).

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12 (random-current derivative / backbone estimate).
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1 (connection
  representation).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, Theorem 17.5.1, p. 312.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **F1 — monomial factorization of the weight**: the random-current weight is
`β`-homogeneous of degree `|n|`,
`w_β(n) = β^{|n|} · w_1(n)` with `w_1(n) = ∏_e J^{n e} / (n e)!`.
Per edge `(β J)^{n e} = β^{n e} J^{n e}` (`mul_pow`); the `β`-powers collect to
`β^{∑_e n e} = β^{|n|}` (`Finset.prod_pow_eq_pow_sum`) and the residual product is
`w_1(n)`. (FFS Chapter 12 / Aizenman 1982.) -/
theorem Current.weight_eq_pow_total_mul_weight_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) (β J : ℝ) :
    n.weight G Λ β J = β ^ (Current.total G Λ n) * n.weight G Λ 1 J := by
  unfold Current.weight Current.total
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [one_mul, mul_pow]
  ring

set_option linter.unusedDecidableInType false in
/-- **F2 — monomial factorization of the doubled summand**: the both-sourcefree
summand is `β`-homogeneous of degree `|M|`,
`D_β(M) = β^{|M|} · D_1(M)`.
Each inner summand `w_β(m) w_β(M − m)` factors (F1 twice) as
`β^{|m| + |M − m|} w_1(m) w_1(M − m)`, and `|m| + |M − m| = |M|`
(`Current.total_add_sub_of_le`, valid since `m ≤ M`) makes the common factor
`β^{|M|}` independent of the summation index, so `Finset.mul_sum` factors it out.
(FFS Chapter 12 / Aizenman 1982.) -/
theorem Current.doubledSourcefreeSummand_eq_pow_total_mul (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (β J : ℝ) (M : Current G Λ) :
    Current.doubledSourcefreeSummand G Λ β J M
      = β ^ (Current.total G Λ M) * Current.doubledSourcefreeSummand G Λ 1 J M := by
  classical
  unfold Current.doubledSourcefreeSummand
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_filter, Current.mem_subFinset_iff] at hm
  have hle : m ≤ M := hm.1
  rw [Current.weight_eq_pow_total_mul_weight_one G Λ m β J,
    Current.weight_eq_pow_total_mul_weight_one G Λ (M - m) β J,
    ← Current.total_add_sub_of_le G Λ hle, pow_add]
  ring

set_option linter.unusedDecidableInType false in
/-- **Non-negativity of the doubled summand**: for `0 ≤ β J` each inner product
`w_β(m) w_β(M − m)` is non-negative (`Current.weight_nonneg`), so `D_β(M) ≥ 0`. -/
theorem Current.doubledSourcefreeSummand_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ} (hβJ : 0 ≤ β * J)
    (M : Current G Λ) :
    0 ≤ Current.doubledSourcefreeSummand G Λ β J M := by
  simp only [Current.doubledSourcefreeSummand]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (Current.weight_nonneg G Λ hβJ m) (Current.weight_nonneg G Λ hβJ (M - m))

set_option linter.unusedDecidableInType false in
/-- **F3 — monotonicity in `β`**: for `0 ≤ β ≤ β'` and `0 ≤ J`,
`D_β(M) ≤ D_{β'}(M)`.
By F2 both sides are `β^{|M|} D_1(M)` and `β'^{|M|} D_1(M)` with `D_1(M) ≥ 0`
(from `0 ≤ 1 · J`), and `β^{|M|} ≤ β'^{|M|}` (`pow_le_pow_left₀`). -/
theorem Current.doubledSourcefree_mono_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β β' J : ℝ}
    (hβ : 0 ≤ β) (hββ' : β ≤ β') (hJ : 0 ≤ J) (M : Current G Λ) :
    Current.doubledSourcefreeSummand G Λ β J M
      ≤ Current.doubledSourcefreeSummand G Λ β' J M := by
  rw [Current.doubledSourcefreeSummand_eq_pow_total_mul G Λ β J M,
    Current.doubledSourcefreeSummand_eq_pow_total_mul G Λ β' J M]
  have hD1 : 0 ≤ Current.doubledSourcefreeSummand G Λ 1 J M :=
    Current.doubledSourcefreeSummand_nonneg G Λ (by simpa using hJ) M
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ hββ' _) hD1

set_option linter.unusedDecidableInType false in
/-- **M1 — the `k ≤ 2^k` majorant step**: for `0 ≤ β` and `0 ≤ J`,
`(|M| : ℝ) · D_β(M) ≤ D_{2β}(M)`.
By F2, `|M| D_β(M) = |M| β^{|M|} D_1(M)` and
`D_{2β}(M) = (2β)^{|M|} D_1(M) = 2^{|M|} β^{|M|} D_1(M)`; since `|M| ≤ 2^{|M|}`
(`Nat.lt_two_pow_self`) and `β^{|M|} D_1(M) ≥ 0`, the claim follows. Uses `0 ≤ β`
and `0 ≤ J` separately (not only `0 ≤ β J`). (FFS Chapter 12.) -/
theorem Current.total_mul_doubledSourcefree_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (M : Current G Λ) :
    (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M
      ≤ Current.doubledSourcefreeSummand G Λ (2 * β) J M := by
  rw [Current.doubledSourcefreeSummand_eq_pow_total_mul G Λ β J M,
    Current.doubledSourcefreeSummand_eq_pow_total_mul G Λ (2 * β) J M, mul_pow]
  have hD1 : 0 ≤ Current.doubledSourcefreeSummand G Λ 1 J M :=
    Current.doubledSourcefreeSummand_nonneg G Λ (by simpa using hJ) M
  have hbase : 0 ≤ β ^ (Current.total G Λ M) * Current.doubledSourcefreeSummand G Λ 1 J M :=
    mul_nonneg (pow_nonneg hβ _) hD1
  have hcast : (Current.total G Λ M : ℝ) ≤ (2 : ℝ) ^ (Current.total G Λ M) := by
    calc (Current.total G Λ M : ℝ)
        ≤ ((2 ^ (Current.total G Λ M) : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self)
      _ = (2 : ℝ) ^ (Current.total G Λ M) := by push_cast; ring
  calc (Current.total G Λ M : ℝ)
        * (β ^ (Current.total G Λ M) * Current.doubledSourcefreeSummand G Λ 1 J M)
      ≤ (2 : ℝ) ^ (Current.total G Λ M)
        * (β ^ (Current.total G Λ M) * Current.doubledSourcefreeSummand G Λ 1 J M) :=
        mul_le_mul_of_nonneg_right hcast hbase
    _ = (2 : ℝ) ^ (Current.total G Λ M) * β ^ (Current.total G Λ M)
        * Current.doubledSourcefreeSummand G Λ 1 J M := by ring

set_option linter.unusedDecidableInType false in
/-- **M2 — summability of the total-weighted summand**: for `0 ≤ β`, `0 ≤ J`,
`Summable (fun M => (|M| : ℝ) · D_β(M))`.
Dominated by the known-summable `D_{2β}` (M1 plus non-negativity), which is
`Current.summable_doubledSourcefree` at inverse temperature `2β` (valid since
`0 ≤ (2β) J`). (FFS Chapter 12.) -/
theorem Current.summable_total_mul_doubledSourcefree (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {β J : ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    Summable (fun M : Current G Λ =>
      (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M) := by
  have h2βJ : 0 ≤ (2 * β) * J := mul_nonneg (by positivity) hJ
  refine Summable.of_nonneg_of_le (g := fun M : Current G Λ =>
      (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M) ?_ ?_
    (Current.summable_doubledSourcefree G Λ h2βJ)
  · intro M
    exact mul_nonneg (Nat.cast_nonneg _)
      (Current.doubledSourcefreeSummand_nonneg G Λ (mul_nonneg hβ hJ) M)
  · intro M
    exact Current.total_mul_doubledSourcefree_le G Λ hβ hJ M

set_option linter.unusedDecidableInType false in
/-- **D1 — the total-mass `β`-derivative**: for `0 < β` and `0 ≤ J`,
`HasDerivAt (fun β' => ∑'_M D_{β'}(M)) ((1/β) · ∑'_M |M| D_β(M)) β`.
`hasDerivAt_tsum_of_isPreconnected` on the open preconnected window
`Ioo (β/2) (2β) ⊂ (0, ∞)`: the termwise derivative is C3′
(`Current.hasDerivAt_doubledSourcefreeSummand_beta`, valid as `β' ≠ 0` on the
window), dominated for all `y` in the window by the fixed
`u(M) = (2/β) |M| D_{2β}(M)` (from `1/y ≤ 2/β` and F3 `D_y ≤ D_{2β}`, summable by
M2), with base point `β`. The returned `∑'_M (|M|/β) D_β(M)` is rewritten to
`(1/β) ∑'_M |M| D_β(M)` (`tsum_mul_left`). (FFS Chapter 12 / GJ §17.5.) -/
theorem Current.hasDerivAt_tsum_doubledSourcefree_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (J : ℝ) {β : ℝ}
    (hβ : 0 < β) (hJ : 0 ≤ J) :
    HasDerivAt (fun β' => ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β' J M)
      (1 / β * ∑' M : Current G Λ,
        (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M) β := by
  classical
  set t : Set ℝ := Set.Ioo (β / 2) (2 * β) with ht
  have hmem : β ∈ t := ⟨by linarith, by linarith⟩
  set u : Current G Λ → ℝ := fun M =>
    2 / β * ((Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ (2 * β) J M)
    with hu_def
  have hu : Summable u := by
    exact (Current.summable_total_mul_doubledSourcefree G Λ (by linarith) hJ).mul_left (2 / β)
  have hg : ∀ (M : Current G Λ) (y : ℝ), y ∈ t →
      HasDerivAt (fun β' => Current.doubledSourcefreeSummand G Λ β' J M)
        ((Current.total G Λ M : ℝ) / y * Current.doubledSourcefreeSummand G Λ y J M) y := by
    intro M y hy
    exact Current.hasDerivAt_doubledSourcefreeSummand_beta G Λ M J (by
      have : 0 < y := lt_trans (by linarith) hy.1
      exact this.ne')
  have hg' : ∀ (M : Current G Λ) (y : ℝ), y ∈ t →
      ‖(Current.total G Λ M : ℝ) / y * Current.doubledSourcefreeSummand G Λ y J M‖ ≤ u M := by
    intro M y hy
    have hy0 : 0 < y := lt_trans (by linarith) hy.1
    have hyJ : 0 ≤ y * J := mul_nonneg hy0.le hJ
    have hDy : 0 ≤ Current.doubledSourcefreeSummand G Λ y J M :=
      Current.doubledSourcefreeSummand_nonneg G Λ hyJ M
    have h1 : (1 : ℝ) / y ≤ 2 / β := by
      rw [div_le_div_iff₀ hy0 hβ]
      nlinarith [hy.1]
    have h2 : Current.doubledSourcefreeSummand G Λ y J M
        ≤ Current.doubledSourcefreeSummand G Λ (2 * β) J M :=
      Current.doubledSourcefree_mono_beta G Λ hy0.le (le_of_lt hy.2) hJ M
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hy0.le) hDy)]
    calc (Current.total G Λ M : ℝ) / y * Current.doubledSourcefreeSummand G Λ y J M
        = (Current.total G Λ M : ℝ) * (1 / y) * Current.doubledSourcefreeSummand G Λ y J M := by
          ring
      _ ≤ (Current.total G Λ M : ℝ) * (2 / β)
          * Current.doubledSourcefreeSummand G Λ (2 * β) J M := by
          apply mul_le_mul _ h2 hDy (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = u M := by rw [hu_def]; ring
  have hg0 : Summable (fun M : Current G Λ =>
      Current.doubledSourcefreeSummand G Λ β J M) :=
    Current.summable_doubledSourcefree G Λ (mul_nonneg hβ.le hJ)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg'
    hmem hg0 hmem
  have hval : (1 : ℝ) / β * ∑' M : Current G Λ,
        (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M
      = ∑' M : Current G Λ,
          (Current.total G Λ M : ℝ) / β * Current.doubledSourcefreeSummand G Λ β J M := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun M => by ring)
  rw [hval]
  exact key

set_option linter.unusedDecidableInType false in
/-- **D2 — the connected-mass `β`-derivative**: for `0 < β`, `0 ≤ J`, over the
reachability subtype `{M // (M.toSimpleGraph).Reachable x y}`,
`HasDerivAt (fun β' => ∑'_{x↔y} D_{β'}(M)) ((1/β) · ∑'_{x↔y} |M| D_β(M)) β`.
Identical to D1 over the subtype: the summability inputs `u`/`g0` transport from
D1's whole-space versions by `Summable.comp_injective` (via `Subtype.val`
injective), and C3′ applies per element (its reachability witness `M.2` is inert
for the derivative). (FFS Chapter 12 / GJ §17.5.) -/
theorem Current.hasDerivAt_tsum_reachable_doubledSourcefree_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (x y : ↑Λ) (J : ℝ)
    {β : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) :
    HasDerivAt (fun β' => ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledSourcefreeSummand G Λ β' J (M : Current G Λ))
      (1 / β * ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        (Current.total G Λ (M : Current G Λ) : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) β := by
  classical
  set t : Set ℝ := Set.Ioo (β / 2) (2 * β) with ht
  have hmem : β ∈ t := ⟨by linarith, by linarith⟩
  set u : Current G Λ → ℝ := fun M =>
    2 / β * ((Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ (2 * β) J M)
    with hu_def
  have hu : Summable (fun M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y} =>
      u (M : Current G Λ)) := by
    have hwhole : Summable u :=
      (Current.summable_total_mul_doubledSourcefree G Λ (by linarith) hJ).mul_left (2 / β)
    exact hwhole.comp_injective Subtype.val_injective
  have hg : ∀ (M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y}) (yv : ℝ), yv ∈ t →
      HasDerivAt (fun β' => Current.doubledSourcefreeSummand G Λ β' J (M : Current G Λ))
        ((Current.total G Λ (M : Current G Λ) : ℝ) / yv
          * Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ)) yv := by
    intro M yv hyv
    exact Current.hasDerivAt_doubledSourcefreeSummand_beta G Λ (M : Current G Λ) J (by
      have : 0 < yv := lt_trans (by linarith) hyv.1
      exact this.ne')
  have hg' : ∀ (M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y}) (yv : ℝ), yv ∈ t →
      ‖(Current.total G Λ (M : Current G Λ) : ℝ) / yv
          * Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ)‖
        ≤ u (M : Current G Λ) := by
    intro M yv hyv
    have hy0 : 0 < yv := lt_trans (by linarith) hyv.1
    have hyJ : 0 ≤ yv * J := mul_nonneg hy0.le hJ
    have hDy : 0 ≤ Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ) :=
      Current.doubledSourcefreeSummand_nonneg G Λ hyJ _
    have h1 : (1 : ℝ) / yv ≤ 2 / β := by
      rw [div_le_div_iff₀ hy0 hβ]
      nlinarith [hyv.1]
    have h2 : Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ)
        ≤ Current.doubledSourcefreeSummand G Λ (2 * β) J (M : Current G Λ) :=
      Current.doubledSourcefree_mono_beta G Λ hy0.le (le_of_lt hyv.2) hJ _
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hy0.le) hDy)]
    calc (Current.total G Λ (M : Current G Λ) : ℝ) / yv
          * Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ)
        = (Current.total G Λ (M : Current G Λ) : ℝ) * (1 / yv)
          * Current.doubledSourcefreeSummand G Λ yv J (M : Current G Λ) := by ring
      _ ≤ (Current.total G Λ (M : Current G Λ) : ℝ) * (2 / β)
          * Current.doubledSourcefreeSummand G Λ (2 * β) J (M : Current G Λ) := by
          apply mul_le_mul _ h2 hDy (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = u (M : Current G Λ) := by rw [hu_def]; ring
  have hg0 : Summable (fun M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y} =>
      Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) :=
    (Current.summable_doubledSourcefree G Λ (mul_nonneg hβ.le hJ)).comp_injective
      Subtype.val_injective
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg'
    hmem hg0 hmem
  have hval : (1 : ℝ) / β * ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        (Current.total G Λ (M : Current G Λ) : ℝ)
          * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          (Current.total G Λ (M : Current G Λ) : ℝ) / β
            * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun M => by ring)
  rw [hval]
  exact key

set_option linter.unusedDecidableInType false in
/-- **Stage D capstone — the ratio-derivative identity**: for `x ≠ y ∈ Λ`,
`0 < β`, `0 ≤ J`, and `hpos : 0 < ⟨σ_xσ_y⟩_Λ` (i.e. `x, y` in the same component
of `inducedGraph G Λ`),
\[
  \partial_\beta\log\langle\sigma_x\sigma_y\rangle_\Lambda
    = \frac{1}{2\beta}\Big(\frac{\sum'_{x\leftrightarrow y}|M|D}
        {\sum'_{x\leftrightarrow y}D}
      - \frac{\sum'_M|M|D}{\sum'_M D}\Big).
\]
Route: the unconditional representation `⟨σσ⟩² = N/Z`
(`Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond`,
`N = ∑'_{x↔y}D`, `Z = ∑'_M D`) gives, via `Real.log_pow` (so
`log⟨σσ⟩ = ½ log⟨σσ⟩²`, no positivity needed for this step) and `Real.log_div`,
the eventual identity `log⟨σσ⟩ = ½(log N − log Z)` on a neighbourhood of `β`
where `Z > 0` (automatic) and `N > 0` (from `hpos` at `β`, spread to a
neighbourhood by continuity of `N`, since `N` is differentiable by D2).
Differentiating `½(log N − log Z)` by `HasDerivAt.log` on D2/D1 (with
`Z = (weightSum ∅)² > 0` and `N = ⟨σσ⟩² Z > 0`), `HasDerivAt.sub` and
`HasDerivAt.const_mul`, then transferring along the eventual identity
(`Filter.EventuallyEq.hasDerivAt_iff`), yields the claim. (FFS Chapter 12 /
Aizenman 1982 Lemma 4.1 / GJ §17.5, Theorem 17.5.1, p. 312.) -/
theorem Current.hasDerivAt_log_correlation_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {x y : ↑Λ} (hxy : x ≠ y)
    (J : ℝ) {β : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J)
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}) :
    HasDerivAt
      (fun β' => Real.log
        (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y}))
      (1 / (2 * β) *
        ((∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
              (Current.total G Λ (M : Current G Λ) : ℝ)
                * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
            / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
                Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
          - (∑' M : Current G Λ,
                (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
              / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M))
      β := by
  classical
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  -- The two `∑'`-derivatives (D1 over all `M`, D2 over the connection subtype).
  have hD1 := Current.hasDerivAt_tsum_doubledSourcefree_beta G Λ J hβ hJ
  have hD2 := Current.hasDerivAt_tsum_reachable_doubledSourcefree_beta G Λ x y J hβ hJ
  -- Positivity of the total mass `Z = ∑'_M D_β`.
  have hZpos : 0 < ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M := by
    rw [← Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ]
    exact pow_pos (Current.weightSum_empty_pos G Λ hβJ) 2
  -- Positivity of the connected mass `N = ∑'_{x↔y} D_β` from `hpos`.
  have hrepβ := Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond
    G Λ hxy hβJ
  have hNeq : (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      = correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
          * ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M :=
    ((eq_div_iff hZpos.ne').mp hrepβ).symm
  have hNpos : 0 < ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
      Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
    rw [hNeq]; exact mul_pos (pow_pos hpos 2) hZpos
  -- Log-derivatives of `N` and `Z`, combined with the `½` prefactor.
  have hlogN := hD2.log hNpos.ne'
  have hlogZ := hD1.log hZpos.ne'
  have hcomb := (hlogN.sub hlogZ).const_mul (1 / 2 : ℝ)
  -- On a neighbourhood of `β`, `log⟨σσ⟩ = ½(log N − log Z)`.
  have hev0 : ∀ᶠ β' in nhds β, (0 : ℝ) < β' := Ioi_mem_nhds hβ
  have hevN : ∀ᶠ β' in nhds β,
      (0 : ℝ) < ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledSourcefreeSummand G Λ β' J (M : Current G Λ) :=
    continuousAt_const.eventually_lt hD2.continuousAt hNpos
  have heEq : (fun β' => Real.log
        (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y}))
      =ᶠ[nhds β] (fun β' => 1 / 2 *
        (Real.log (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
              Current.doubledSourcefreeSummand G Λ β' J (M : Current G Λ))
          - Real.log (∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β' J M))) := by
    filter_upwards [hev0, hevN] with β' hβ'0 hN'
    have hβ'J : 0 ≤ β' * J := mul_nonneg hβ'0.le hJ
    have hZ'pos : 0 < ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β' J M := by
      rw [← Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβ'J]
      exact pow_pos (Current.weightSum_empty_pos G Λ hβ'J) 2
    have hrep' := Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond
      G Λ hxy hβ'J
    have hlp : Real.log (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y})
        = 1 / 2 * Real.log
            (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y} ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hlp, hrep', Real.log_div hN'.ne' hZ'pos.ne']
  rw [Filter.EventuallyEq.hasDerivAt_iff heEq]
  convert hcomb using 1
  have hβ0 : β ≠ 0 := hβ.ne'
  have hN0 : (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
      Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) ≠ 0 := hNpos.ne'
  have hZ0 : (∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M) ≠ 0 := hZpos.ne'
  field_simp

set_option linter.unusedDecidableInType false in
/-- **Sign-collapse — excess-current nonnegativity.**  For `x ≠ y ∈ Λ`, `0 < β`,
`0 ≤ J`, and `hpos : 0 < ⟨σ_xσ_y⟩_Λ`, conditioning on the connection event
`{x ↔ y}` can only *increase* the `D`-normalised expected total current:
\[
  \mathbb{E}\,\lvert M\rvert
    = \frac{\sum'_M \lvert M\rvert D}{\sum'_M D}
  \;\le\;
  \frac{\sum'_{x\leftrightarrow y}\lvert M\rvert D}{\sum'_{x\leftrightarrow y}D}
    = \mathbb{E}^{x\leftrightarrow y}\,\lvert M\rvert .
\]
Equivalently `0 ≤ ∂_β log⟨σ_xσ_y⟩_Λ`, i.e. the lower-direction (sign) half of the
OZ log-derivative estimate `hLogLip` of Theorem 17.5.1's lower-semicontinuous
half.

Proof: by GKS-II (`correlation_monotoneOn_beta`) the map `β' ↦ ⟨σ_xσ_y⟩_Λ` is
monotone on `Ici 0` and positive at `β` (`hpos`), so `β' ↦ log⟨σ_xσ_y⟩_Λ` is
nondecreasing on `Ioi β`; hence every right slope of it at `β` is `≥ 0`.  The
Stage-D derivative `∂_β log⟨σσ⟩ = (1/2β)(E^{x↔y}|M| − E|M|)`
(`Current.hasDerivAt_log_correlation_beta`) is the right-limit of those slopes, so
it is `≥ 0`; dividing out `1/(2β) > 0` gives `E|M| ≤ E^{x↔y}|M|`.

This is only the lower-direction collapse of the excess current; the matching
*upper* bound `E^{x↔y}|M| − E|M| ≤ C·d(0,x)` (OZ backbone length, FFS Ch. 12 /
Aizenman 1982) is off-book and is not addressed here.  (GJ §17.5,
Theorem 17.5.1, p. 312.) -/
theorem Current.doubledSourcefree_excess_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {x y : ↑Λ} (hxy : x ≠ y)
    (J : ℝ) {β : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J)
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}) :
    (∑' M : Current G Λ,
          (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
        / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M
      ≤ (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            (Current.total G Λ (M : Current G Λ) : ℝ)
              * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
          / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
              Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
  classical
  -- Stage-D ratio-derivative identity: the derivative of `g` equals `(1/2β)·excess`.
  have hderiv := Current.hasDerivAt_log_correlation_beta G Λ hxy J hβ hJ hpos
  set g : ℝ → ℝ := fun β' =>
    Real.log (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y})
    with hg
  set L : ℝ := 1 / (2 * β) *
      ((∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            (Current.total G Λ (M : Current G Λ) : ℝ)
              * Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
          / ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
              Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)
        - (∑' M : Current G Λ,
              (Current.total G Λ M : ℝ) * Current.doubledSourcefreeSummand G Λ β J M)
            / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M)
    with hL
  -- GKS-II ⟹ `g` is nondecreasing on `Ioi β` (using `hpos` for positivity of `log`).
  have hmono : ∀ x' ∈ Set.Ioi β, g β ≤ g x' := by
    intro x' hx'
    have hx'0 : (0 : ℝ) < x' := hβ.trans hx'
    have hcorr : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
        ≤ correlation (inducedGraph G Λ) (⟨J, 0, x'⟩ : IsingParams ℝ) {x, y} :=
      correlation_monotoneOn_beta (inducedGraph G Λ) J hJ {x, y}
        (Set.mem_Ici.mpr hβ.le) (Set.mem_Ici.mpr hx'0.le) (le_of_lt hx')
    simp only [hg]
    exact Real.log_le_log hpos hcorr
  -- The Stage-D derivative is the right-limit of the (nonnegative) slopes of `g` at `β`.
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi β)
    (by simp)).mp hderiv.hasDerivWithinAt
  have hLnonneg : 0 ≤ L := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with x' hx'
    rw [slope_def_field]
    have hnum : 0 ≤ g x' - g β := by linarith [hmono x' hx']
    have hden : 0 ≤ x' - β := by have := Set.mem_Ioi.mp hx'; linarith
    exact div_nonneg hnum hden
  -- Divide out the positive prefactor `1/(2β)`.
  have hcoef : (0 : ℝ) < 1 / (2 * β) := by positivity
  rw [hL] at hLnonneg
  have hexcess := (mul_nonneg_iff_of_pos_left hcoef).mp hLnonneg
  linarith

end Ambient
end IsingModel
