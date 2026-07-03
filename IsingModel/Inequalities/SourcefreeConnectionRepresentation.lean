import IsingModel.Inequalities.CurrentConnectivityRepresentation

/-!
# Sourcefree (`∅/∅`) connection representation of the *squared* two-point function

This file assembles **Stage C, brick 1 (C1′, corrected)** of the random-current
build toward the lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue
#4386, thread #4418): Aizenman's *sourcefree* connection representation of the
**square** of the two-point function,
\[
  \langle\sigma_x\sigma_y\rangle_{\Lambda}^{2}\cdot Z_\emptyset^{2}
  = \sum_{\substack{M\ :\ x\leftrightarrow y}} D(M),
  \qquad
  D(M):=\!\!\sum_{\substack{m\le M,\ \partial m=\emptyset,\ \partial(M-m)=\emptyset}}\!\!
        w(m)\,w(M-m),
\]
the both-sourcefree (`∅/∅`) ensemble form, equivalently
`⟨σ_xσ_y⟩² = ℙ^{∅,∅}[x ↔ y]` after dividing by `Z_∅² > 0`.

**Correctness fix.** An earlier version of this file stated the identity for the
*first power* `⟨σ_xσ_y⟩` and gated it on `hswitch : ∑_{x↔y} N = ∑_{x↔y} D`, where
`N` is Stage B's `{x,y}/∅` summand. That gate is **false**: a single-edge
computation gives `∑_{x↔y} N = sinh t cosh t` but `∑_{x↔y} D = sinh² t`, so
`hswitch` would force `cosh t = sinh t`. The genuine Aizenman/FFS switching lemma
identifies the `∅/∅` connected mass with the **square**
(`∑_{x↔y} D = (Z_{x,y})² = ⟨σσ⟩² Z_∅²`). The corrected representation and TRUE
gate `hswitch'` (below) fix this power error.

All sourcefree scaffolding is proven **unconditionally**:
* `Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree` (U1):
  `Z_∅² = ∑'_M D(M)` (Stage A brick 2 with `A = B = ∅`);
* `Current.summable_doubledSourcefree` (U2): `Summable D` (hoisted Stage A
  summability with `A = B = ∅`);
* `Current.tsum_reachable_doubledSourcefree_le_weightSum_empty_sq` (U3): the
  Griffiths upper bound `∑'_{x ↔ y} D(M) ≤ Z_∅²`
  (`ℙ^{∅,∅}[x ↔ y] ≤ 1`), a genuine subtype restriction of the non-negative
  summable family `D` (via `tsum_comp_le_tsum_of_inj` + U1 + U2).

The both-`{x,y}`-sourced feedstock `W(M)` (`Current.doubledPairSummand`) drives
the corrected square:
* `Current.weightSum_pair_sq_eq_tsum_doubled_pair` (U1′):
  `(Z_{x,y})² = ∑'_M W(M)` (Stage A brick 2 with `A = B = {x,y}`);
* `Current.doubled_pair_pair_sum_eq_zero_of_not_reachable` (B2′): `W` vanishes
  off the connection set (the `∂m = {x,y}` conjunct forces `Reachable x y`,
  exactly as for Stage B's `N`), so `∑'_M W = ∑'_{x↔y} W`.

The sole deferred content — the genuine Aizenman *switching* bijection that
identifies the `{x,y}/{x,y}` connected mass with the `∅/∅` connected mass (a
global, `M`-changing 𝔽₂ cycle-space count; there is provably no per-current
shortcut, since the existing `m ↦ M − m` involution is only the trivial
relabelling on `∂M = ∅`) — is isolated as a single named hypothesis `hswitch'`:
\[
  \sum_{M\,:\,x\leftrightarrow y} W(M)
    = \sum_{M\,:\,x\leftrightarrow y} D(M),
\]
the `A = B` instance of the fixed-`M` switching identity. This mirrors the
accepted #4402/#4403 gate-then-discharge pattern (reduce to one clearly-named
textbook ingredient). The gated capstone
`Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree`
and its probability-form corollary
`Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div` follow
immediately from U1′, B2′ and `hswitch'`.

**Scope: C1′ yields no new rate.** It is the structural bridge converting the
two-point *lower* bound into a sourcefree percolation
connection-probability lower bound `ℙ^{∅,∅}[x ↔ y] ≥ rate`; it does not by
itself beat the existing `tanh(β J)^{d(x,y)}` bound. Because the connection
probability equals `⟨σσ⟩²` (not `⟨σσ⟩`), its decay rate is `2 · m`, so Stage C3
rate accounting carries an absolute factor `2`. Discharging `hswitch'` (the
fixed-`M` switching bijection) is Stage C2.1, and the sharp
connection-probability lower bound is Stage C3 (the OZ mechanism); both are
genuine multi-PR research.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1
  (`⟨σ_xσ_y⟩² = ℙ^{∅,∅}[x ↔ y]`).
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Chapter 12 (Theorem 9.35, Lemma 9.36).
* Glimm–Jaffe, *Quantum Physics*, §17.5 Theorem 17.5.1 (p. 312).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Both-sourcefree (`∅/∅`) doubled inner pairing summand `D(M)`**: for a
doubled current `M`, the finite inner sum over splittings `M = m + (M − m)`
with *both* pieces sourcefree (`∂m = ∅` and `∂(M − m) = ∅`),
`D(M) = ∑_{m ≤ M, ∂m = ∅, ∂(M − m) = ∅} w(m) w(M − m)`. This is the `A = B = ∅`
case of the doubled inner pairing appearing in Stage A brick 2; it is
supported on `∂M = ∅` and is the summand of the sourcefree connection
representation. (Aizenman 1982 Lemma 4.1 / FFS Chapter 12.) -/
noncomputable def Current.doubledSourcefreeSummand
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (M : Current G Λ) : ℝ :=
  ∑ m ∈ (Current.subFinset G Λ M).filter
      (fun m => m.sources G Λ = ∅ ∧ (M - m).sources G Λ = ∅),
    m.weight G Λ β J * (M - m).weight G Λ β J

set_option linter.unusedDecidableInType false in
/-- **Both-`{x,y}`-sourced doubled inner pairing summand `W(M)`**: for a
doubled current `M`, the finite inner sum over splittings `M = m + (M − m)`
with *both* pieces sourced at `{x, y}` (`∂m = {x,y}` and `∂(M − m) = {x,y}`),
`W(M) = ∑_{m ≤ M, ∂m = {x,y}, ∂(M − m) = {x,y}} w(m) w(M − m)`. This is the
`A = B = {x,y}` case of the doubled inner pairing appearing in Stage A brick 2;
since `∂m = ∂(M − m) = {x,y}` forces `∂M = {x,y} △ {x,y} = ∅`, it is supported
on `∂M = ∅`, and each `∂m = {x,y}` conjunct forces `Reachable x y`. It is the
feedstock for the *square* of the two-point function
(`(Z_{x,y})² = ∑'_M W(M)`). (Aizenman 1982 Lemma 4.1 / FFS Chapter 12.) -/
noncomputable def Current.doubledPairSummand
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (x y : ↑Λ) (β J : ℝ) (M : Current G Λ) : ℝ :=
  ∑ m ∈ (Current.subFinset G Λ M).filter
      (fun m => m.sources G Λ = {x, y} ∧ (M - m).sources G Λ = {x, y}),
    m.weight G Λ β J * (M - m).weight G Λ β J

set_option linter.unusedDecidableInType false in
/-- **U1: sourcefree self-pairing**: for non-negative coupling `0 ≤ β J` (zero
field `h = 0`), the square of the sourcefree partition mass equals the `tsum`
of the both-sourcefree summand,
`(weightSum ∅)² = ∑'_M D(M)`. Proof: `pow_two` rewrites the square as
`weightSum ∅ · weightSum ∅`, which the Stage A brick 2 identity
`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset` (with
`A = B = ∅`) equates to `∑'_M D(M)` by definition of
`Current.doubledSourcefreeSummand`. (Aizenman 1982 Lemma 4.1 / GJ §17.5.) -/
theorem Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M := by
  simp only [Current.doubledSourcefreeSummand, pow_two]
  exact Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset G Λ ∅ ∅ hβJ

set_option linter.unusedDecidableInType false in
/-- **U1′: `{x,y}` self-pairing (feedstock for the square)**: for `0 ≤ β J`
(zero field `h = 0`), the square of the `{x,y}` partition mass equals the
`tsum` of the both-`{x,y}`-sourced summand,
`(weightSum {x,y})² = ∑'_M W(M)`. Proof: `pow_two` rewrites the square as
`weightSum {x,y} · weightSum {x,y}`, which the Stage A brick 2 identity
`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset` (with
`A = B = {x,y}`) equates to `∑'_M W(M)` by definition of
`Current.doubledPairSummand`. (Aizenman 1982 Lemma 4.1 / GJ §17.5.) -/
theorem Current.weightSum_pair_sq_eq_tsum_doubled_pair
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (x y : ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Current.weightSum G Λ {x, y} β J ^ 2
      = ∑' M : Current G Λ, Current.doubledPairSummand G Λ x y β J M := by
  simp only [Current.doubledPairSummand, pow_two]
  exact Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset G Λ {x, y} {x, y} hβJ

set_option linter.unusedDecidableInType false in
/-- **U2: summability of the sourcefree summand**: for `0 ≤ β J`, the
both-sourcefree summand `D` is `Summable`. Proof: the hoisted Stage A
summability `Current.summable_doubled_subFinset` with `A = B = ∅`, unfolding
`Current.doubledSourcefreeSummand`. -/
theorem Current.summable_doubledSourcefree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Summable (Current.doubledSourcefreeSummand G Λ β J) := by
  unfold Current.doubledSourcefreeSummand
  exact Current.summable_doubled_subFinset G Λ ∅ ∅ hβJ

set_option linter.unusedDecidableInType false in
/-- **B2′: non-connecting doubled currents contribute zero to `W`**: if the
support graph of `M` does *not* connect `x` to `y` (with `x ≠ y`), then the
both-`{x,y}`-sourced summand `W(M)` vanishes. Proof (a verbatim mirror of Stage
B's `Current.doubled_pair_sum_eq_zero_of_not_reachable`, using only the first
conjunct): the filtered `Finset` is empty — any `m ≤ M` with `∂m = {x,y}` would
force `Reachable x y` by `Current.reachable_of_subFinset_sources_pair`,
contradicting the hypothesis; hence `Finset.filter_false_of_mem` and
`Finset.sum_empty`. -/
theorem Current.doubled_pair_pair_sum_eq_zero_of_not_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (M : Current G Λ)
    (hnr : ¬ (M.toSimpleGraph G Λ).Reachable x y) :
    Current.doubledPairSummand G Λ x y β J M = 0 := by
  simp only [Current.doubledPairSummand]
  rw [Finset.filter_false_of_mem
      (fun m hm hfilter => hnr
        (Current.reachable_of_subFinset_sources_pair G Λ hxy hm hfilter.1)),
    Finset.sum_empty]

set_option linter.unusedDecidableInType false in
/-- **U3: Griffiths upper bound `ℙ^{∅,∅}[x ↔ y] ≤ 1`**: for `0 ≤ β J`, the
connection-restricted sourcefree sum is bounded by the total,
`∑'_{M : x ↔ y} D(M) ≤ (weightSum ∅)²`. Unlike Stage B, the `Reachable x y`
restriction is a **genuine** strict restriction here (a both-sourcefree
current `∂M = ∅` need not connect `x` to `y`), so this is an honest subtype
inequality, not a no-op. Proof: `D ≥ 0` (product of non-negative weights,
`Current.weight_nonneg`), so the subtype sum over the `Reachable` currents is
`≤` the total by `tsum_comp_le_tsum_of_inj` (injectivity of `Subtype.val`,
summability from U2), and the total equals `(weightSum ∅)²` by U1. This is the
trivial `≤ 1` direction; the lower bound is Stage C3 (deferred). -/
theorem Current.tsum_reachable_doubledSourcefree_le_weightSum_empty_sq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
        Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      ≤ Current.weightSum G Λ ∅ β J ^ 2 := by
  have hD_nonneg : ∀ M : Current G Λ,
      0 ≤ Current.doubledSourcefreeSummand G Λ β J M := by
    intro M
    simp only [Current.doubledSourcefreeSummand]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (Current.weight_nonneg G Λ hβJ m)
        (Current.weight_nonneg G Λ hβJ (M - m))
  calc (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      ≤ ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M :=
        tsum_comp_le_tsum_of_inj
          (Current.summable_doubledSourcefree G Λ hβJ) hD_nonneg
          Subtype.val_injective
    _ = Current.weightSum G Λ ∅ β J ^ 2 :=
        (Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ).symm

set_option linter.unusedDecidableInType false in
/-- **C1′ capstone: sourcefree connection representation of the square, gated**:
for `x ≠ y ∈ Λ` and `0 ≤ β J` (zero field `h = 0`), *given* the TRUE Aizenman
switching gate `hswitch'`
(`∑'_{M : x ↔ y} W(M) = ∑'_{M : x ↔ y} D(M)`, equating the `{x,y}/{x,y}`
connected sum with the `∅/∅` connected sum),
\[
  \langle\sigma_x\sigma_y\rangle_{\Lambda}^{2}\cdot (weightSum\ ∅)^{2}
    = \sum_{M\,:\,x\leftrightarrow y} D(M).
\]
Proof chain: (ii) squaring the ratio
`correlation {x,y} = weightSum {x,y} / weightSum ∅`
(`correlation_inducedGraph_eq_weightSum_ratio`) and clearing the positive
`weightSum ∅` (`Current.weightSum_empty_pos`) gives
`correlation {x,y}² · (weightSum ∅)² = (weightSum {x,y})²`; (i)
`(weightSum {x,y})² = ∑'_M W(M)` by U1′
(`Current.weightSum_pair_sq_eq_tsum_doubled_pair`); (iii)
`∑'_M W = ∑'_{x↔y} W` since `W` is supported on the connection set (B2′,
`Current.doubled_pair_pair_sum_eq_zero_of_not_reachable`, via
`tsum_subtype_eq_of_support_subset`); (iv) rewrite by `hswitch'`.

`hswitch'` is the genuine switching content — the `A = B` instance of the
fixed-`M` Aizenman switching identity, a global 𝔽₂ cycle-space cardinality with
no per-current shortcut (the existing `m ↦ M − m` involution is only the trivial
relabelling on `∂M = ∅`) — and is deferred as an explicit hypothesis (Stage
C2.1), not an axiom. (Aizenman 1982 Lemma 4.1 / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hswitch' :
      (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledPairSummand G Λ x y β J (M : Current G Λ))
        = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
        * Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ) := by
  classical
  have hW : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
  -- Step (ii): the left side equals `(weightSum {x,y})²`.
  have h1 : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
        * Current.weightSum G Λ ∅ β J ^ 2
      = Current.weightSum G Λ {x, y} β J ^ 2 := by
    rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y}, div_pow]
    field_simp
  -- Step (iii): `W` is supported on the `x ↔ y` connection set (B2′).
  have hsupp : Function.support (Current.doubledPairSummand G Λ x y β J)
      ⊆ {M | (M.toSimpleGraph G Λ).Reachable x y} := by
    intro M hM
    rw [Function.mem_support] at hM
    by_contra hnr
    exact hM (Current.doubled_pair_pair_sum_eq_zero_of_not_reachable G Λ hxy M hnr)
  -- Steps (i)+(iii)+(iv): `(weightSum {x,y})² = ∑'_M W = ∑'_{x↔y} W = ∑'_{x↔y} D`.
  rw [h1, Current.weightSum_pair_sq_eq_tsum_doubled_pair G Λ x y hβJ,
    ← tsum_subtype_eq_of_support_subset hsupp]
  exact hswitch'

set_option linter.unusedDecidableInType false in
/-- **C1′ probability form (gated), total-mass denominator**: dividing the
squared capstone by the positive **total both-sourcefree mass** `∑'_M D(M)`,
for `x ≠ y`, `0 ≤ β J`, and the TRUE switching gate `hswitch'`,
\[
  \langle\sigma_x\sigma_y\rangle_{\Lambda}^{2}
    = \frac{\sum_{M\,:\,x\leftrightarrow y} D(M)}{\sum_M D(M)}
    = \mathbb{P}^{\emptyset,\emptyset}[x \leftrightarrow y],
\]
the genuine Aizenman/FFS sourcefree connection-*probability* form: the *square*
of the two-point function is the ratio of the connected (`x ↔ y`) `∅/∅` mass to
the *total* `∅/∅` mass. Proof: rewrite the denominator
`(weightSum ∅)² = ∑'_M D(M)` via **U1**
(`Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree`), so the positive
denominator is the total mass; then `eq_div_iff` against it and the gated
squared capstone
`Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree`.
(Aizenman 1982 Lemma 4.1 / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.correlation_sq_eq_tsum_reachable_doubledSourcefree_div
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} (hxy : x ≠ y) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hswitch' :
      (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledPairSummand G Λ x y β J (M : Current G Λ))
        = ∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ)) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ^ 2
      = (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
            Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
          / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M := by
  have hU1 : Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M :=
    Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ
  have hden : 0 < ∑' M : Current G Λ,
      Current.doubledSourcefreeSummand G Λ β J M :=
    hU1 ▸ pow_pos (Current.weightSum_empty_pos G Λ hβJ) 2
  rw [eq_div_iff hden.ne', ← hU1]
  exact Current.correlation_sq_mul_weightSum_empty_sq_eq_tsum_reachable_sourcefree
    G Λ hxy hβJ hswitch'

set_option linter.unusedDecidableInType false in
/-- **C1′ Griffiths bound `⟨σσ⟩² = ℙ^{∅,∅}[x ↔ y] ≤ 1`, probability-ratio
form**: for `0 ≤ β J`, the sourcefree connection probability — the ratio of the
connected (`x ↔ y`) `∅/∅` mass to the total `∅/∅` mass, which under the
corrected representation equals `⟨σ_xσ_y⟩²` — is at most `1`,
\[
  \frac{\sum_{M\,:\,x\leftrightarrow y} D(M)}{\sum_M D(M)} \le 1 .
\]
This is the honest `≤ 1` half of the connection probability (unconditional; no
`hswitch'`, no `x ≠ y` needed), consistent with `|⟨σσ⟩| = |tanh(β J)| ≤ 1`.
Proof: `div_le_one` against the positive total mass `∑'_M D(M) > 0` (from **U1**
+ `Current.weightSum_empty_pos`), with numerator `≤` denominator supplied by
**U3** (`Current.tsum_reachable_doubledSourcefree_le_weightSum_empty_sq`, itself
using **U2** summability) after rewriting `(weightSum ∅)² = ∑'_M D(M)` via
**U1**. The matching lower bound is the genuine Stage C3 content (deferred).
(Aizenman 1982 Lemma 4.1 / FFS Chapter 12 / GJ §17.5.) -/
theorem Current.tsum_reachable_doubledSourcefree_div_tsum_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {x y : ↑Λ} {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
        / ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M
      ≤ 1 := by
  have hU1 : Current.weightSum G Λ ∅ β J ^ 2
      = ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M :=
    Current.weightSum_empty_sq_eq_tsum_doubled_sourcefree G Λ hβJ
  have hden : 0 < ∑' M : Current G Λ,
      Current.doubledSourcefreeSummand G Λ β J M :=
    hU1 ▸ pow_pos (Current.weightSum_empty_pos G Λ hβJ) 2
  rw [div_le_one hden]
  calc (∑' M : {M : Current G Λ // (M.toSimpleGraph G Λ).Reachable x y},
          Current.doubledSourcefreeSummand G Λ β J (M : Current G Λ))
      ≤ Current.weightSum G Λ ∅ β J ^ 2 :=
        Current.tsum_reachable_doubledSourcefree_le_weightSum_empty_sq G Λ hβJ
    _ = ∑' M : Current G Λ, Current.doubledSourcefreeSummand G Λ β J M := hU1

end Ambient
end IsingModel
