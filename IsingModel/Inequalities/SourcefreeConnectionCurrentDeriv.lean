import IsingModel.Inequalities.SourcefreeConnectionRepresentation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Field

/-!
# Current-weight `β`-differentiation identity (Stage C3′)

This file assembles **Stage C, brick C3′** of the random-current build toward the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue #4386, thread
#4418): the elementary `β`-differentiation identity for the random-current
weight, and its lift to the both-sourcefree doubled inner summand `D(M)`.

With induced edge set `E = (inducedGraph G Λ).edgeSet` (finite), uniform coupling
`J`, inverse temperature `β` and the current weight
`w_β(n) = ∏_{e ∈ E} (β J)^{n e} / (n e)!` (`Current.weight`), the **total current
size** is `|n| = ∑_{e ∈ E} n e` (`Current.total`, introduced here) and the
identities are, for `β ≠ 0`,
\[
  \partial_\beta w_\beta(n) = \frac{|n|}{\beta}\, w_\beta(n),
  \qquad
  \partial_\beta D_\beta(M) = \frac{|M|}{\beta}\, D_\beta(M).
\]
The `D(M)` identity is the crux: because every splitting `M = m + (M - m)`
satisfies `|m| + |M - m| = |M|` (pointwise additivity, `Current.total_add_sub_of_le`),
each doubled-weight summand carries the *same* total size `|M|`, so `D_β(M)` scales
like a single monomial of degree `|M|` in `β J`.

## Main results

* `Current.total` — the total current size `|n| = ∑_e n e`.
* `Current.total_add_sub_of_le` — `|m| + |M - m| = |M|` for `m ≤ M`.
* `Current.hasDerivAt_weight_beta` (C3′ atomic) —
  `HasDerivAt (w_· (n)) ((|n| / β) · w_β(n)) β`.
* `Current.hasDerivAt_doubledSourcefreeSummand_beta` (C3′ consumable) —
  `HasDerivAt (D_· (M)) ((|M| / β) · D_β(M)) β`.

This brick supplies **only** the differentiation identity; it does *not* close the
`hLogLip` estimate (that needs the excess-current backbone bound, a later brick).

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, §17.5 Theorem 17.5.1 (p. 312).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Total current size** `|n| := ∑_{e ∈ E} n e`: the ℕ-valued sum of the
current values over all induced-graph edges. This is the total-current
observable pulled down by `β`-differentiation of the weight
`w_β(n) = ∏_e (β J)^{n e} / (n e)!`; distinct from the per-vertex
`Current.degreeAt`. (FFS Chapter 12 / Aizenman 1982.) -/
def Current.total (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) : ℕ :=
  ∑ e : (inducedGraph G Λ).edgeSet, n e

omit [DecidableEq V] in
/-- **Zero current has total size `0`**: every summand vanishes. -/
@[simp]
theorem Current.zero_total (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (0 : Current G Λ).total G Λ = 0 := by
  unfold Current.total
  simp

omit [DecidableEq V] in
/-- **Total size is additive across a truncated splitting**: for `m ≤ M`
(pointwise), `|m| + |M - m| = |M|`. Each edge contributes
`m e + (M e - m e) = M e` by `Nat.add_sub_cancel'`, then the sums combine via
`Finset.sum_add_distrib`. This is the constant-`|M|` observation making
`D_β(M)` differentiate cleanly. -/
theorem Current.total_add_sub_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {M m : Current G Λ} (h : m ≤ M) :
    Current.total G Λ m + Current.total G Λ (M - m) = Current.total G Λ M := by
  unfold Current.total
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Current.sub_apply]
  exact Nat.add_sub_cancel' (h e)

omit [DecidableEq V] in
/-- **C3′ atomic — the weight `β`-derivative**: for every current `n`, every
coupling `J`, and every `β ≠ 0`,
`∂_β w_β(n) = (|n| / β) · w_β(n)`, i.e.
`HasDerivAt (fun β' => w_{β'}(n)) ((|n| / β) · w_β(n)) β`.
Each edge factor `φ_e(β') = (β' J)^{n e} / (n e)!` is a monomial with
`φ_e'(β) = (n e / β) · φ_e(β)` (needs `β ≠ 0`); the finite product rule
(`HasDerivAt.finset_prod`) and `Finset.prod_erase_mul` collapse the sum of the
per-edge factors to `(∑_e n e) / β = |n| / β`. (Aizenman 1982 Lemma 4.1.) -/
theorem Current.hasDerivAt_weight_beta (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) (J : ℝ) {β : ℝ}
    (hβ : β ≠ 0) :
    HasDerivAt (fun β' => n.weight G Λ β' J)
      ((Current.total G Λ n : ℝ) / β * n.weight G Λ β J) β := by
  classical
  -- Per-edge derivative in the target `(n e / β) · φ_e(β)` form.
  have hedge : ∀ e ∈ (Finset.univ : Finset (inducedGraph G Λ).edgeSet),
      HasDerivAt (fun β' => (β' * J) ^ (n e) / ((n e).factorial : ℝ))
        ((n e : ℝ) / β * ((β * J) ^ (n e) / ((n e).factorial : ℝ))) β := by
    intro e _
    have hbase : HasDerivAt (fun β' => β' * J) J β := by
      simpa using (hasDerivAt_id β).mul_const J
    have h3 : HasDerivAt (fun β' => (β' * J) ^ (n e) / ((n e).factorial : ℝ))
        (((n e : ℝ) * (β * J) ^ (n e - 1) * J) / ((n e).factorial : ℝ)) β :=
      (hbase.pow (n e)).div_const _
    have heq : (n e : ℝ) / β * ((β * J) ^ (n e) / ((n e).factorial : ℝ))
        = ((n e : ℝ) * (β * J) ^ (n e - 1) * J) / ((n e).factorial : ℝ) := by
      rcases Nat.eq_zero_or_pos (n e) with h0 | hpos
      · simp [h0]
      · have hfe : ((n e).factorial : ℝ) ≠ 0 := by
          exact_mod_cast (n e).factorial_ne_zero
        have hk : (β * J) ^ (n e) = (β * J) ^ (n e - 1) * (β * J) := by
          conv_lhs => rw [← Nat.sub_add_cancel hpos]
          rw [pow_succ]
        rw [hk]
        field_simp
    rw [heq]; exact h3
  -- Finite product rule over the edge set.
  have hprod := HasDerivAt.fun_finset_prod hedge
  convert hprod using 1
  -- Collapse the sum of per-edge factors to `|n| / β · w_β(n)`.
  simp only [smul_eq_mul]
  have hterm : ∀ e ∈ (Finset.univ : Finset (inducedGraph G Λ).edgeSet),
      (∏ j ∈ (Finset.univ : Finset (inducedGraph G Λ).edgeSet).erase e,
          (β * J) ^ (n j) / ((n j).factorial : ℝ))
        * ((n e : ℝ) / β * ((β * J) ^ (n e) / ((n e).factorial : ℝ)))
      = (n e : ℝ) / β * n.weight G Λ β J := by
    intro e _
    have hw : n.weight G Λ β J
        = (∏ j ∈ (Finset.univ : Finset (inducedGraph G Λ).edgeSet).erase e,
            (β * J) ^ (n j) / ((n j).factorial : ℝ))
          * ((β * J) ^ (n e) / ((n e).factorial : ℝ)) :=
      (Finset.prod_erase_mul Finset.univ
        (fun j => (β * J) ^ (n j) / ((n j).factorial : ℝ)) (Finset.mem_univ e)).symm
    rw [hw]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum]
  rfl

/-- **C3′ consumable — the doubled-summand `β`-derivative**: for every doubled
current `M` and every `β ≠ 0`,
`∂_β D_β(M) = (|M| / β) · D_β(M)`, i.e.
`HasDerivAt (fun β' => D_{β'}(M)) ((|M| / β) · D_β(M)) β`.
`D_β(M)` is a finite sum over splittings `M = m + (M - m)` (both pieces
sourcefree) of `w_β(m) · w_β(M - m)`; each summand differentiates by the product
rule and `Current.hasDerivAt_weight_beta` to
`((|m| + |M - m|) / β) · w_β(m) w_β(M - m) = (|M| / β) · w_β(m) w_β(M - m)`
(the constant-`|M|` collapse of `Current.total_add_sub_of_le`), so summing
(`HasDerivAt.sum`) pulls out the common factor `|M| / β`. (Aizenman 1982
Lemma 4.1 / GJ §17.5.) -/
theorem Current.hasDerivAt_doubledSourcefreeSummand_beta (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) (J : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    HasDerivAt (fun β' => Current.doubledSourcefreeSummand G Λ β' J M)
      ((Current.total G Λ M : ℝ) / β
        * Current.doubledSourcefreeSummand G Λ β J M) β := by
  classical
  -- Per-splitting derivative, with the constant-`|M|` collapse.
  have hmem : ∀ m ∈ (Current.subFinset G Λ M).filter
        (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
      HasDerivAt (fun β' => m.weight G Λ β' J * (M - m).weight G Λ β' J)
        ((Current.total G Λ M : ℝ) / β
          * (m.weight G Λ β J * (M - m).weight G Λ β J)) β := by
    intro m hm
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hm
    have hle : m ≤ M := hm.1
    have hprodm := (Current.hasDerivAt_weight_beta G Λ m J hβ).mul
      (Current.hasDerivAt_weight_beta G Λ (M - m) J hβ)
    convert hprodm using 1
    rw [← Current.total_add_sub_of_le G Λ hle]
    push_cast
    ring
  -- Finite sum rule over the sourcefree splittings.
  have hsum := HasDerivAt.fun_sum hmem
  convert hsum using 1
  simp only [Current.doubledSourcefreeSummand, Finset.mul_sum]

end Ambient
end IsingModel
