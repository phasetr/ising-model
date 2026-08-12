import IsingModel.Inequalities.SourcefreeConnectionRepresentation
import IsingModel.RandomCurrent.Switching.PerCurrentVanishing

/-!
# Unconditional discharge of the Aizenman switching gate `hswitch'` (Stage C2.1e + C2.2)

This file is the **closing brick of Stage C2** (Aizenman switching) of the
random-current build toward the lower-semicontinuous half of Glimm–Jaffe
Theorem 17.5.1 (issue #4386, thread #4418). It discharges the switching gate
`hswitch'` of Stage C1 (`SourcefreeConnectionRepresentation.lean`)
**unconditionally**, turning the *sourcefree connection representation of the
square of the two-point function*
\[
  \langle\sigma_x\sigma_y\rangle_\Lambda^2 = \mathbb{P}^{\emptyset,\emptyset}[x\leftrightarrow y]
\]
(Aizenman 1982, Proposition 3.1, eq. (3.2), p. 6) into an unconditional
theorem.

## Structure

* **C2.1e — per-current `W(M) = D(M)`**
  (`Current.doubledPairSummand_eq_doubledSourcefreeSummand_of_reachable`): for
  `x ≠ y` reachable in `M.toSimpleGraph`, the both-`{x,y}`-sourced doubled
  summand `W(M)` equals the both-sourcefree summand `D(M)`. Case split on
  `∂M = ∅`:
  - If `∂M = ∅`, then for `m ≤ M`, `∂(M − m) = ∅ △ ∂m = ∂m`
    (`sub_sources_eq_symmDiff` + `bot_symmDiff`), so each filter's second
    conjunct is redundant and both reduce to the single-source sets
    `subFinset_with_source M {x,y}` and `subFinset_with_source M ∅`. The weight
    bridge `weight_mul_weight_eq_weight_add_mul_jointFactor` +
    `add_sub_cancel_of_le` factors out `w(M)`, and C2.1d
    (`sum_jointFactor_pair_eq_sum_jointFactor_empty_of_reachable`,
    `f_M({x,y}) = f_M(∅)`) closes the goal.
  - If `∂M ≠ ∅`, both filters are empty (`W` needs
    `∂(M − m) = ∂M △ {x,y} = {x,y}`, i.e. `∂M = ∅` by `symmDiff_eq_right`;
    `D` needs `∂(M − m) = ∂M △ ∅ = ∂M = ∅`), so `W(M) = 0 = D(M)`.
* **C2.2 — gate discharge**
  (`Current.tsum_reachable_doubledPair_eq_doubledSourcefree`): `tsum_congr`
  over the reachability subtype lifts C2.1e to the exact `tsum` equality that is
  the gate `hswitch'`.
* **Unconditional capstones**: feeding the discharged gate to the Stage C1 gated
  theorems removes their `hswitch'` hypothesis, yielding
  `Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree_uncond`
  and the probability-ratio form
  `Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond`.

All content is elementary source-set (`symmDiff`) algebra plus C2.1d and the C1
gated theorems; TRUE (numeric-checked: single edge `∑W = ∑D = sinh² t`,
two-edge path `W = D = t⁴`), axiom-free, no `sorry`.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 3.2, p. 7,
  eq. (3.5) (the switching lemma); Proposition 3.1, eq. (3.2), p. 6 (the
  sourcefree connection representation).
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, Theorem 17.5.1, p. 312.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **C2.1e: per-current `W(M) = D(M)`**: for `x ≠ y` connected in the support
graph `M.toSimpleGraph`, the both-`{x,y}`-sourced doubled summand
`W(M) = doubledPairSummand x y M` equals the both-sourcefree summand
`D(M) = doubledSourcefreeSummand M`. Case split on `∂M = ∅`:
* If `∂M = ∅`: for `m ≤ M`, `∂(M − m) = symmDiff ∅ (∂m) = ∂m`
  (`sub_sources_eq_symmDiff` + `bot_symmDiff`), so each filter's second conjunct
  is redundant and both filters collapse to the single-source sets
  `subFinset_with_source M {x,y}` / `subFinset_with_source M ∅`
  (`Finset.filter_congr`). The weight bridge
  `weight_mul_weight_eq_weight_add_mul_jointFactor` with
  `add_sub_cancel_of_le` rewrites each term `w(m) w(M − m) = w(M) · jointFactor`,
  and `Finset.mul_sum` factors out `w(M)`, giving
  `W(M) = w(M) f_M({x,y})`, `D(M) = w(M) f_M(∅)`; C2.1d
  (`sum_jointFactor_pair_eq_sum_jointFactor_empty_of_reachable`) closes it.
* If `∂M ≠ ∅`: both filters are empty
  (`Finset.filter_false_of_mem`): a `W`-term with `∂m = {x,y}` would force
  `∂(M − m) = symmDiff (∂M) {x,y} = {x,y} ↔ ∂M = ⊥` (`symmDiff_eq_right`),
  contradicting `∂M ≠ ∅`; a `D`-term with `∂m = ∅` would force
  `∂(M − m) = symmDiff (∂M) ∅ = ∂M = ∅`, again a contradiction. Hence
  `W(M) = 0 = D(M)`. (Aizenman 1982 Lemma 3.1, p. 7, at `A = B = {x,y}` /
  FFS Chapter 12.) -/
theorem Current.doubledPairSummand_eq_doubledSourcefreeSummand_of_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) {x y : ↑Λ} (hxy : x ≠ y) (β J : ℝ)
    (hreach : (M.toSimpleGraph G Λ).Reachable x y) :
    Current.doubledPairSummand G Λ x y β J M
      = Current.doubledSourcefreeSummand G Λ β J M := by
  classical
  by_cases hM : M.sources G Λ = ∅
  · -- `∂M = ∅`: both filters collapse to a single source constraint.
    have key : ∀ A : Finset ↑Λ,
        (∑ m ∈ (Current.subFinset G Λ M).filter
            (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = A),
          m.weight G Λ β J * (M - m).weight G Λ β J)
          = M.weight G Λ β J
              * ∑ m ∈ Current.subFinset_with_source G Λ M A,
                  Current.jointFactor G Λ m (M - m) := by
      intro A
      have hfilter : (Current.subFinset G Λ M).filter
            (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = A)
          = Current.subFinset_with_source G Λ M A := by
        unfold Current.subFinset_with_source
        refine Finset.filter_congr (fun m hm => ?_)
        rw [Current.mem_subFinset_iff] at hm
        have hsub : (M - m).sources G Λ = m.sources G Λ := by
          rw [Current.sub_sources_eq_symmDiff G Λ hm, hM, ← Finset.bot_eq_empty,
            bot_symmDiff]
        unfold Current.HasSources
        rw [hsub]
        tauto
      rw [hfilter, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Current.mem_subFinset_with_source_iff] at hm
      rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
        Current.add_sub_cancel_of_le G Λ hm.1]
    simp only [Current.doubledPairSummand, Current.doubledSourcefreeSummand]
    rw [key {x, y}, key ∅]
    congr 1
    exact Current.sum_jointFactor_pair_eq_sum_jointFactor_empty_of_reachable
      G Λ M hxy hreach
  · -- `∂M ≠ ∅`: both filters are empty.
    have hWempty : (Current.subFinset G Λ M).filter
          (fun m => m.sources G Λ = {x, y} ∧ (M - m).sources G Λ = {x, y}) = ∅ := by
      refine Finset.filter_false_of_mem (fun m hm hp => ?_)
      rw [Current.mem_subFinset_iff] at hm
      obtain ⟨hm1, hm2⟩ := hp
      rw [Current.sub_sources_eq_symmDiff G Λ hm, hm1, symmDiff_eq_right] at hm2
      exact hM (hm2.trans Finset.bot_eq_empty)
    have hDempty : (Current.subFinset G Λ M).filter
          (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅) = ∅ := by
      refine Finset.filter_false_of_mem (fun m hm hp => ?_)
      rw [Current.mem_subFinset_iff] at hm
      obtain ⟨hm1, hm2⟩ := hp
      rw [Current.sub_sources_eq_symmDiff G Λ hm, hm1, ← Finset.bot_eq_empty,
        symmDiff_bot] at hm2
      exact hM (hm2.trans Finset.bot_eq_empty)
    simp only [Current.doubledPairSummand, Current.doubledSourcefreeSummand]
    rw [hWempty, hDempty, Finset.sum_empty]

set_option linter.unusedDecidableInType false in
/-- **C2.2: unconditional discharge of the switching gate `hswitch'`**: for
`x ≠ y`, the reachability-restricted `tsum` of the both-`{x,y}`-sourced summand
`W` equals that of the both-sourcefree summand `D`,
`∑'_{M : x ↔ y} W(M) = ∑'_{M : x ↔ y} D(M)`. This is *exactly* the gate
`hswitch'` of Stage C1. Proof: `tsum_congr` over the reachability subtype
`{M // (M.toSimpleGraph).Reachable x y}` — each element's membership witness
`M.2` supplies the reachability hypothesis of C2.1e
(`doubledPairSummand_eq_doubledSourcefreeSummand_of_reachable`), giving
`W(M) = D(M)` termwise; no summability is required.
(Aizenman 1982 Lemma 3.2, p. 7, eq. (3.5) / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.tsum_reachable_doubledPair_eq_doubledSourcefree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) (β J : ℝ) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledPairSummand G Λ x y β J (M : Current G Λ))
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) :=
  tsum_congr (fun M =>
    Current.doubledPairSummand_eq_doubledSourcefreeSummand_of_reachable
      G Λ (M : Current G Λ) hxy β J M.2)

set_option linter.unusedDecidableInType false in
/-- **C1′ capstone, UNCONDITIONAL**: for `x ≠ y ∈ Λ` and `0 ≤ β J` (zero field
`h = 0`), *with no switching hypothesis*,
\[
  \langle\sigma_x\sigma_y\rangle_\Lambda^2 \cdot (\text{weightSum }\emptyset)^2
    = \sum_{M\,:\,x\leftrightarrow y} D(M).
\]
Proof: feed the discharged gate C2.2
(`Current.tsum_reachable_doubledPair_eq_doubledSourcefree`) to the Stage C1
gated capstone
`Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree`,
removing its `hswitch'` hypothesis. (Aizenman 1982 Proposition 3.1, eq. (3.2),
p. 6 / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree_uncond
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
        * Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) :=
  Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree
    G Λ hxy hβJ
    (Current.tsum_reachable_doubledPair_eq_doubledSourcefree G Λ hxy β J)

set_option linter.unusedDecidableInType false in
/-- **C1′ probability form, UNCONDITIONAL** (`⟨σσ⟩² = ℙ^{∅,∅}[x ↔ y]`): for
`x ≠ y` and `0 ≤ β J`, *with no switching hypothesis*,
\[
  \langle\sigma_x\sigma_y\rangle_\Lambda^2
    = \frac{\sum_{M\,:\,x\leftrightarrow y} D(M)}{\sum_M D(M)}
    = \mathbb{P}^{\emptyset,\emptyset}[x \leftrightarrow y].
\]
The *square* of the two-point function is the ratio of the connected (`x ↔ y`)
`∅/∅` mass to the *total* `∅/∅` mass — the genuine Aizenman/FFS sourcefree
connection-probability representation, now a theorem with no hypothesis. Proof:
feed the discharged gate C2.2
(`Current.tsum_reachable_doubledPair_eq_doubledSourcefree`) to the Stage C1
gated probability form
`Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div`.
(Aizenman 1982 Proposition 3.1, eq. (3.2), p. 6 / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div_uncond
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
      = (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
          / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M :=
  Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div
    G Λ hxy hβJ
    (Current.tsum_reachable_doubledPair_eq_doubledSourcefree G Λ hxy β J)

end Ambient
end IsingModel
