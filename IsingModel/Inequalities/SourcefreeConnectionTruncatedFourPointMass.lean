import IsingModel.RandomCurrent.Switching.GlobalSwitchingLimit

/-!
# Truncated four-point mass as the `x ↮ y` doubled sum (OZ Wall #2, Stage P2, Step P2-i)

This file formalises **Step P2-i** — the *second-switching / truncated four-point
mass identity* — of the Ornstein–Zernike ("Wall #2") route towards the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (§17.5, p. 312; issue
#4386, thread #4418, group 1a lsc/backbone).  It is the sibling of the Step P1
capstone (`Current.doubledSourcefree_edgeExcess_eq_truncated4pt`,
`SourcefreeConnectionEdgeReachableLeg.lean`, PR #4482) and re-uses that file's
local `key` device essentially verbatim.

## What is proved

For distinct sites, the **single-pairing truncated four-point mass**
`W_{uvxy} = Z_{{u,v,x,y}} · Z_∅ − Z_{{u,v}} · Z_{{x,y}}`
(`Z_A = Current.weightSum G Λ A β J`) equals the doubled `({u,v,x,y}, ∅)`-sourced
sum restricted to the currents whose support graph does **not** connect `x` to
`y`:

* **(a) core, `symmDiff` form** (`hxy` only,
  `Current.truncated4PointMass_symmDiff_eq_tsum_notReachable`):
  `Z_{{u,v} △ {x,y}} · Z_∅ − Z_{{u,v}} · Z_{{x,y}}
    = ∑'_{K : x ↮ y} ∑_{m ≤ K, ∂m = {u,v} △ {x,y}, ∂(K − m) = ∅} w(m) w(K − m)`;
* **(b) four-point form** (adds `Disjoint {u,v} {x,y}`,
  `Current.truncated4PointMass_eq_tsum_notReachable`): rewriting
  `{u,v} △ {x,y} = {u,v,x,y}` yields the mass `W_{uvxy}` on the left (GJ eq. of
  Lemma P2mass in `rc-oz-stageP2-backbone-bijection.tex`);
* **(c) nonnegativity** (`Current.truncated4PointMass_nonneg`):
  `0 ≤ W_{uvxy}` — a `tsum` of nonnegative terms (a **Griffiths-II-type**
  single-pairing mass).

## Naming caveat (`W` is single-pairing, not the true `U₄`)

`W_{uvxy}` subtracts **only the single pairing** `{u,v} | {x,y}`
(`Z_{{u,v}} · Z_{{x,y}}`).  It is therefore a *single-pairing truncated
four-point mass*, and is **not** the genuine Ursell / Lebowitz four-point
function `U₄`, which subtracts **all three** pairings
`{u,v}|{x,y}`, `{u,x}|{v,y}`, `{u,y}|{v,x}`.  Do **not** read the
nonnegativity `0 ≤ W_{uvxy}` as `−U₄ ≥ 0`: it is the weaker, positive-flavour
Griffiths-II statement for a single pairing, sufficient only for the P2 backbone
entry consumed by Step P2-ii.

## Proof (companion note `rc-oz-stageP2-backbone-bijection.tex`, Lemma P2mass)

Reading both products as `tsum`s over doubled currents
(`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset`, twice) and
subtracting term-by-term (`tsum_sub`, both summable via
`Current.summable_doubled_subFinset`), the summand
`Hfull K − G' K` (with `Hfull` the `({u,v} △ {x,y}, ∅)`-sourced inner sum and
`G'` the `({u,v}, {x,y})`-sourced inner sum) satisfies the pointwise identity
`Hfull K − G' K = 1_{x ↮ y}(K) · Hfull K`:

* both `Hfull K ≠ 0` and `G' K ≠ 0` force `∂K = {u,v} △ {x,y}`
  (`Current.sub_sources_eq_symmDiff`);
* on `x ↔ y` the general-source character switch P1-α
  (`Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable`, ghost pair
  `{x,y}`, base `{u,v}`) gives `Hfull K = G' K`, so the difference vanishes;
* on `x ↮ y` every term of `G'` has `∂(K − m) = {x,y}` with `K − m ≤ K`, so
  `Current.reachable_of_subFinset_sources_pair` would force `x ↔ y`, a
  contradiction; hence `G' K = 0` and the difference is `Hfull K`.

`tsum_subtype` then collapses `∑'_K 1_{x ↮ y}(K) · Hfull K` to the `x ↮ y`
subtype sum.  (Aizenman 1982 §4, Eqs. (4.8)–(4.10); FFS Thm 9.35 read in the
general-source direction.)

## Scope (honest limitation)

This is the **entry fragment** of the P2 backbone bijection: it produces exactly
the `{u,v,x,y}`-sourced, `x ↮ y` doubled mass that Step P2-ii consumes.  It is an
**equality with a nonnegativity corollary** (lower-flavour, matching the
already-merged `Current.doubledSourcefree_excess_nonneg`, #4475).  It is
**structural** and does **not** by itself deliver any *upper* bound on
`∂_β log ⟨σ_x σ_y⟩`; hence it does **not** advance the `h_LogLip` upper Lipschitz
bound.  The upper direction is Wall **B3** (the backbone-tail / pivotal-edge count
bound, `E^{x↔y}[#pivotal] ≤ K' · d(x,y)`), which is **gated on exponential decay /
mass-gap input** and is irreducibly research (separate multi-session build).  The
genuine **P2-ii backbone bijection** (weight bookkeeping against Aizenman 1982
Eq. (4.12) / FFS Ch. 12) is likewise **out of scope of this PR**.

## References

* Aizenman, M. (1982) Geometric analysis of φ⁴ fields and Ising models. I,
  Comm. Math. Phys. **86**, 1–48; §4, Eqs. (4.8)–(4.10) (source switching;
  truncated four-point representation).
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Thm 9.35 (switching), Ch. 12 (backbone representation).
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5 Theorem 17.5.1 (p. 312).

(Issue #4386, thread #4418; math note `rc-oz-stageP2-backbone-bijection.tex`.)
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **P2-i core (second-switching mass identity, `symmDiff` form)**: for
`0 ≤ β J` and `x ≠ y`, the second-switching mass with base source `{u,v}` and
ghost pair `{x,y}` equals the `({u,v} △ {x,y}, ∅)`-sourced doubled sum restricted
to the currents whose support graph does *not* connect `x` to `y`:
`Z_{{u,v} △ {x,y}} · Z_∅ − Z_{{u,v}} · Z_{{x,y}}
  = ∑'_{K : x ↮ y} ∑_{m ≤ K, ∂m = {u,v} △ {x,y}, ∂(K − m) = ∅} w(m) w(K − m)`,
with `Z_A = Current.weightSum G Λ A β J` and `w = Current.weight`.

Proof (companion note `rc-oz-stageP2-backbone-bijection.tex`, Lemma P2mass).
Both products are read as `tsum`s over doubled currents
(`Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset`) and subtracted
term-by-term (`tsum_sub`, summable via `Current.summable_doubled_subFinset`).  The
summand `Hfull K − G' K` (`Hfull` = `({u,v} △ {x,y}, ∅)`-sourced inner sum, `G'` =
`({u,v}, {x,y})`-sourced inner sum) satisfies `Hfull K − G' K = 1_{x ↮ y}(K)·Hfull K`:
both nonzero cases force `∂K = {u,v} △ {x,y}`
(`Current.sub_sources_eq_symmDiff`); on `x ↔ y` the general-source character switch
P1-α (`Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable`) gives
`Hfull K = G' K`; on `x ↮ y` a term of `G'` would force `x ↔ y`
(`Current.reachable_of_subFinset_sources_pair`), so `G' K = 0`.  `tsum_subtype`
collapses the indicator to the subtype sum.

Scope: this is an *equality* (lower-flavour / structural); it does **not** advance
the `h_LogLip` *upper* bound, which is gated on Wall B3 (exponential-decay input).
(Aizenman 1982 §4, Eqs. (4.8)–(4.10); FFS Thm 9.35; Glimm–Jaffe Theorem 17.5.1,
issue #4386.) -/
theorem Current.truncated4PointMass_symmDiff_eq_tsum_notReachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (u v x y : ↑Λ) (hxy : x ≠ y) :
    Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
          * Current.weightSum G Λ (∅ : Finset ↑Λ) β J
        - Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
          * Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J
      = ∑' K : {K : Current G Λ // ¬ (K.toSimpleGraph G Λ).Reachable x y},
          ∑ m ∈ (Current.subFinset G Λ (K : Current G Λ)).filter
              (fun m => m.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y}
                ∧ ((K : Current G Λ) - m).sources G Λ = ∅),
            m.weight G Λ β J * ((K : Current G Λ) - m).weight G Λ β J := by
  classical
  rw [Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset
        G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) ∅ hβJ,
      Current.weightSum_mul_weightSum_eq_tsum_doubled_subFinset
        G Λ ({u, v} : Finset ↑Λ) {x, y} hβJ]
  -- `Hfull` = `({u,v} △ {x,y}, ∅)`-sourced inner sum; `G'` = `({u,v}, {x,y})`-sourced.
  set Hfull : Current G Λ → ℝ := fun K =>
    ∑ m ∈ (Current.subFinset G Λ K).filter
        (fun m => m.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y}
          ∧ (K - m).sources G Λ = ∅),
      m.weight G Λ β J * (K - m).weight G Λ β J with hHfull
  set G' : Current G Λ → ℝ := fun K =>
    ∑ m ∈ (Current.subFinset G Λ K).filter
        (fun m => m.sources G Λ = ({u, v} : Finset ↑Λ) ∧ (K - m).sources G Λ = {x, y}),
      m.weight G Λ β J * (K - m).weight G Λ β J with hG'
  -- Source support: `Hfull K ≠ 0 ⟹ ∂K = {u,v} △ {x,y}`.
  have hsrcHfull : ∀ K : Current G Λ, Hfull K ≠ 0
      → K.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y} := by
    intro K hne
    simp only [hHfull] at hne
    obtain ⟨m, hmmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hmmem
    obtain ⟨hmle, h1, h2⟩ := hmmem
    rw [Current.sub_sources_eq_symmDiff G Λ hmle, h1, ← Finset.bot_eq_empty,
      symmDiff_eq_bot] at h2
    exact h2
  -- Source support: `G' K ≠ 0 ⟹ ∂K = {u,v} △ {x,y}`.
  have hsrcG' : ∀ K : Current G Λ, G' K ≠ 0
      → K.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y} := by
    intro K hne
    simp only [hG'] at hne
    obtain ⟨m, hmmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.mem_filter, Current.mem_subFinset_iff] at hmmem
    obtain ⟨hmle, h1, h2⟩ := hmmem
    rw [Current.sub_sources_eq_symmDiff G Λ hmle, h1] at h2
    have h3 : K.sources G Λ = symmDiff ({x, y} : Finset ↑Λ) ({u, v} : Finset ↑Λ) := by
      have hcg := congrArg (fun s => symmDiff s ({u, v} : Finset ↑Λ)) h2
      simpa [symmDiff_symmDiff_cancel_right] using hcg
    rw [h3]
    exact symmDiff_comm ({x, y} : Finset ↑Λ) ({u, v} : Finset ↑Λ)
  -- β-switch: `Hfull K = G' K` on the reachable event.
  have hswitch : ∀ K : Current G Λ, (K.toSimpleGraph G Λ).Reachable x y
      → Hfull K = G' K := by
    intro K hreachK
    by_cases hK : K.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y}
    · have key : ∀ (A B : Finset ↑Λ), K.sources G Λ = symmDiff A B →
          (∑ m ∈ (Current.subFinset G Λ K).filter
              (fun m => m.sources G Λ = A ∧ (K - m).sources G Λ = B),
            m.weight G Λ β J * (K - m).weight G Λ β J)
            = K.weight G Λ β J
                * ∑ m ∈ Current.subFinset_with_source G Λ K A,
                    Current.jointFactor G Λ m (K - m) := by
        intro A B hAB
        have hfilter : (Current.subFinset G Λ K).filter
              (fun m => m.sources G Λ = A ∧ (K - m).sources G Λ = B)
            = Current.subFinset_with_source G Λ K A := by
          unfold Current.subFinset_with_source
          refine Finset.filter_congr (fun m hm => ?_)
          rw [Current.mem_subFinset_iff] at hm
          unfold Current.HasSources
          constructor
          · rintro ⟨h1, _⟩; exact h1
          · intro h1
            refine ⟨h1, ?_⟩
            rw [Current.sub_sources_eq_symmDiff G Λ hm, hAB, h1, symmDiff_comm A B,
              symmDiff_assoc, symmDiff_self, symmDiff_bot]
        rw [hfilter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Current.mem_subFinset_with_source_iff] at hm
        rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
          Current.add_sub_cancel_of_le G Λ hm.1]
      simp only [hHfull, hG']
      rw [key (symmDiff ({u, v} : Finset ↑Λ) {x, y}) ∅
            (by rw [hK, ← Finset.bot_eq_empty, symmDiff_bot]),
        key ({u, v} : Finset ↑Λ) {x, y} hK]
      congr 1
      exact (Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable
        G Λ K hxy ({u, v} : Finset ↑Λ) hreachK).symm
    · have h1 : Hfull K = 0 := by by_contra hc; exact hK (hsrcHfull K hc)
      have h2 : G' K = 0 := by by_contra hc; exact hK (hsrcG' K hc)
      rw [h1, h2]
  -- `G' K = 0` on the non-connecting event (`{x, y}` sits on the complement leg).
  have hG'zero : ∀ K : Current G Λ, ¬ (K.toSimpleGraph G Λ).Reachable x y
      → G' K = 0 := by
    intro K hnr
    simp only [hG']
    rw [Finset.filter_false_of_mem
        (fun m _ hfilter => hnr
          (Current.reachable_of_subFinset_sources_pair G Λ hxy
            ((Current.mem_subFinset_iff G Λ K (K - m)).mpr (Current.sub_le_self G Λ K m))
            hfilter.2)),
      Finset.sum_empty]
  -- Summability of both cap-free inner sums.
  have hsum1 : Summable Hfull :=
    Current.summable_doubled_subFinset G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) ∅ hβJ
  have hsum2 : Summable G' :=
    Current.summable_doubled_subFinset G Λ ({u, v} : Finset ↑Λ) {x, y} hβJ
  -- Term-by-term difference, then collapse the indicator to the `x ↮ y` subtype sum.
  rw [← hsum1.tsum_sub hsum2,
    show (∑' K : {K : Current G Λ // ¬ (K.toSimpleGraph G Λ).Reachable x y},
            ∑ m ∈ (Current.subFinset G Λ (K : Current G Λ)).filter
                (fun m => m.sources G Λ = symmDiff ({u, v} : Finset ↑Λ) {x, y}
                  ∧ ((K : Current G Λ) - m).sources G Λ = ∅),
              m.weight G Λ β J * ((K : Current G Λ) - m).weight G Λ β J)
          = ∑' K : Current G Λ,
            {K : Current G Λ | ¬ (K.toSimpleGraph G Λ).Reachable x y}.indicator Hfull K
      from tsum_subtype {K : Current G Λ | ¬ (K.toSimpleGraph G Λ).Reachable x y} Hfull]
  refine tsum_congr (fun K => ?_)
  by_cases hR : (K.toSimpleGraph G Λ).Reachable x y
  · rw [Set.indicator_of_notMem (by simpa using hR)]
    linarith [hswitch K hR]
  · rw [Set.indicator_of_mem (by simpa using hR)]
    linarith [hG'zero K hR]

set_option linter.unusedDecidableInType false in
/-- **P2-i four-point form (single-pairing truncated four-point mass identity)**:
for `0 ≤ β J`, `x ≠ y`, and `u, v` disjoint from `x, y` (`Disjoint {u,v} {x,y}`,
hence pairwise-distinct sites), the *single-pairing truncated four-point mass*
`W_{uvxy} = Z_{{u,v,x,y}} · Z_∅ − Z_{{u,v}} · Z_{{x,y}}`
(subtracting **only** the pairing `{u,v} | {x,y}`, so **not** the true
Ursell / Lebowitz `U₄`, which subtracts all three pairings)
(`Z_A = Current.weightSum G Λ A β J`) equals the `({u,v,x,y}, ∅)`-sourced doubled
sum restricted to the currents whose support graph does *not* connect `x` to `y`:
`W_{uvxy}
  = ∑'_{K : x ↮ y} ∑_{m ≤ K, ∂m = {u,v,x,y}, ∂(K − m) = ∅} w(m) w(K − m)`.
This is the Lean realisation of eq. (P2mass) in
`rc-oz-stageP2-backbone-bijection.tex`.

Proof.  Disjointness gives `{u,v} △ {x,y} = {u,v,x,y}`
(`Disjoint.symmDiff_eq_sup`); rewriting both occurrences reduces the claim to the
`symmDiff` core `Current.truncated4PointMass_symmDiff_eq_tsum_notReachable`.

Scope: an *equality* (lower-flavour); it produces the object consumed by the P2-ii
backbone bijection but does **not** advance the `h_LogLip` upper bound, which is
gated on Wall B3 (exponential-decay input).  (Aizenman 1982 §4; FFS Thm 9.35;
Glimm–Jaffe Theorem 17.5.1, issue #4386.) -/
theorem Current.truncated4PointMass_eq_tsum_notReachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (u v x y : ↑Λ) (hxy : x ≠ y)
    (hdisj : Disjoint ({u, v} : Finset ↑Λ) {x, y}) :
    Current.weightSum G Λ ({u, v, x, y} : Finset ↑Λ) β J
          * Current.weightSum G Λ (∅ : Finset ↑Λ) β J
        - Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
          * Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J
      = ∑' K : {K : Current G Λ // ¬ (K.toSimpleGraph G Λ).Reachable x y},
          ∑ m ∈ (Current.subFinset G Λ (K : Current G Λ)).filter
              (fun m => m.sources G Λ = ({u, v, x, y} : Finset ↑Λ)
                ∧ ((K : Current G Λ) - m).sources G Λ = ∅),
            m.weight G Λ β J * ((K : Current G Λ) - m).weight G Λ β J := by
  have hAeq : symmDiff ({u, v} : Finset ↑Λ) {x, y} = {u, v, x, y} := by
    rw [hdisj.symmDiff_eq_sup, Finset.sup_eq_union]
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [← hAeq]
  exact Current.truncated4PointMass_symmDiff_eq_tsum_notReachable G Λ hβJ u v x y hxy

set_option linter.unusedDecidableInType false in
/-- **P2-i nonnegativity (single-pairing truncated four-point mass, Griffiths-II
type)**: for `0 ≤ β J`, `x ≠ y`, and `Disjoint {u,v} {x,y}`, the single-pairing
truncated four-point mass is nonnegative,
`0 ≤ Z_{{u,v,x,y}} · Z_∅ − Z_{{u,v}} · Z_{{x,y}}`.  Because only the single
pairing `{u,v} | {x,y}` is subtracted, this is **not** the true Ursell / Lebowitz
`−U₄ ≥ 0` (which subtracts all three pairings); it is the weaker single-pairing
positivity.

Proof.  By `Current.truncated4PointMass_eq_tsum_notReachable` the mass is a `tsum`
over the `x ↮ y` subtype of finite sums of terms `w(m) · w(K − m)`, each
nonnegative under `0 ≤ β J` (`Current.weight_nonneg`); `Finset.sum_nonneg` and
`tsum_nonneg` close.

Scope: this is a *lower-flavour* corollary (matching
`Current.doubledSourcefree_excess_nonneg`, #4475); it does **not** deliver any
*upper* bound and does **not** advance the `h_LogLip` upper Lipschitz bound (gated
on Wall B3, exponential-decay input).  (Aizenman 1982 §4; Glimm–Jaffe Theorem
17.5.1, issue #4386.) -/
theorem Current.truncated4PointMass_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (u v x y : ↑Λ) (hxy : x ≠ y)
    (hdisj : Disjoint ({u, v} : Finset ↑Λ) {x, y}) :
    0 ≤ Current.weightSum G Λ ({u, v, x, y} : Finset ↑Λ) β J
          * Current.weightSum G Λ (∅ : Finset ↑Λ) β J
        - Current.weightSum G Λ ({u, v} : Finset ↑Λ) β J
          * Current.weightSum G Λ ({x, y} : Finset ↑Λ) β J := by
  rw [Current.truncated4PointMass_eq_tsum_notReachable G Λ hβJ u v x y hxy hdisj]
  refine tsum_nonneg (fun K => Finset.sum_nonneg (fun m _ => ?_))
  exact mul_nonneg (Current.weight_nonneg G Λ hβJ m)
    (Current.weight_nonneg G Λ hβJ ((K : Current G Λ) - m))

end Ambient

end IsingModel
