import IsingModel.Inequalities.ClusterConditioningFiberSplit

/-!
# SL-D brick D1b (foundation): ambient restriction algebra + even-cardinality handshake

This module implements the **design-agnostic foundation** of ingredient **SL-D,
brick D1b** — the restriction/extend-by-zero map on the ambient current type and
its weight/degree/parity/source algebra, together with the even-cardinality
(handshaking) identity for the edge-subset-restricted degree. These are the item-1
and item-2 bricks of the D1b plan (`rc-oz-lemma51-SLD1b-fubini.tex`): the first
standalone verifiable brick (`Current.restrictOn` and its algebra) and the clean
`Finset.sum` parity helper (`Current.degreeOn_sum_eq_two_mul`,
`Current.sourcesOn_card_even`).

## Scope and honest status

D1b is the completion of `SL-D₁` (product Fubini) = D1a's additive source split
(`Current.pivotalFiber_sources_split` / `pivotalFiber_sourcesOn_eq`) turned, via a
restriction/gluing bijection `Φ` and a `tsum` Fubini, into the ensemble
factorisation `Σ_C = (βJ)·Ξ_int·Ξ_ext`. This module delivers only the *foundation*
that any correct D1b needs: the ambient restriction map, its block-weight and
`degreeOn`/`parityOn`/`sourcesOn` invariance, and the handshaking parity of the
restricted source set. It does **not** build the bijection `Φ` nor the `tsum`
Fubini: see the "design blocker" note below.

**Nondegeneracy design blocker — RESOLVED by the symmetric-difference source form.**
The original D1b spec tried to discharge deferred side conditions `x ≠ a`, `y ≠ b`
by "the even-cardinality lemma", which does **not** imply them: `x = a` is
realisable on a pinned pivotal fiber (a source coinciding with the near endpoint of
the pivotal bridge), in which case `sourcesOn (interiorEdges C) M = ∅`, not `{x, a}`.
The corrected design (`.self-local/reports/design-oz-d1b-degeneracy.md`) drops the
nondegeneracy hypotheses entirely and states the source constraints as **symmetric
differences** `sourcesOn (interiorEdges C) M = {x} △ {a}` and
`sourcesOn (interiorEdges Cᶜ) M = {b} △ {y}`
(`Current.pivotalFiber_sourcesOn_symmDiff`, built on the degeneracy-uniform
`Current.sourcesOn_eq_symmDiff`, both in `ClusterConditioningFiberSplit.lean`): the
symmetric difference collapses to `∅` exactly in the degenerate branch `x = a`
(resp. `y = b`), so the forward-landing and reverse-source steps of `Φ` need **no**
nondegeneracy at all. `sourcesOn_card_even` (below) remains a **true** helper but is
no longer on the D1b critical path (it was never able to yield `x ≠ a`, and need not).

The symmetric-difference source split (`pivotalFiber_sourcesOn_symmDiff`, this PR's
increment) is the first verifiable brick of the corrected D1b; the remaining
SL-D₁-completion bricks — the restriction/gluing bijection `Φ` (round-trip via
`Finset.piecewise`, the `reachableCluster` decoupling in both directions, the
reverse `EdgePivotal` reconstruction) and the headline `tsum` Fubini
`Σ_C = (βJ)·Ξ_int·Ξ_ext` (`Equiv.tsum_eq` + `Summable.tsum_mul_tsum`) — are the
next increment, entirely inside the authorised `SL-D₁`.

**Tracked-ingredient status.** Like SL-A/SL-B/SL-C/D1a, this is a *tracked
ingredient* (Group 1a authorisation), buildable and axiom-free, with
reference-count zero into the live capstone. Downstream position: the (future)
Lemma 5.1 → P2-ii → `hLogLip` → the explicitly-tracked lower-semicontinuity half
of GJ Theorem 17.5.1 (§17.5, issue #4386 / thread #4418). Because `SL-D₂`
(the exterior → two-point collapse: conditioned-switching / subgraph-current,
Aizenman Lemma 4.1) **awaits explicit user authorisation**, D1b does **not**
complete Lemma 5.1: `SL-D₂` remains the gate, and this module touches none of it.
The weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current weight of
Friedli–Velenik, eq. (3.45).

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7, eq. (3.45).
* Glimm–Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.5.1, p. 312 (lsc half,
  issue #4386 / thread #4418).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Ambient restriction (extend-by-zero) of a current** to an edge subset `S`:
`restrictOn S n e = n e` for `e ∈ S` and `0` otherwise (`Finset.piecewise S n 0`).
It represents a *block-restricted* current in place, on the single ambient current
type `Current G Λ = E → ℕ`; no "current on a subgraph" is ever formed. This is the
first verifiable brick of ingredient **SL-D₁** (product Fubini) brick D1b (tracked
ingredient, Group 1a; the SL-D₂ conditioned-switching core awaits explicit user
authorisation); weight source FV (3.45). -/
def Current.restrictOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) : Current G Λ :=
  S.piecewise n 0

omit [DecidableEq V] in
/-- **`restrictOn` on `S` is the identity**: for `e ∈ S`, `restrictOn S n e = n e`.
Part of ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.restrictOn_apply_mem (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ)
    {e : (inducedGraph G Λ).edgeSet} (he : e ∈ S) :
    n.restrictOn G Λ S e = n e := by
  unfold Current.restrictOn
  rw [Finset.piecewise_eq_of_mem _ _ _ he]

omit [DecidableEq V] in
/-- **`restrictOn` off `S` vanishes**: for `e ∉ S`, `restrictOn S n e = 0`. Part of
ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.restrictOn_apply_not_mem (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ)
    {e : (inducedGraph G Λ).edgeSet} (he : e ∉ S) :
    n.restrictOn G Λ S e = 0 := by
  unfold Current.restrictOn
  rw [Finset.piecewise_eq_of_notMem _ _ _ he]
  rfl

omit [DecidableEq V] in
/-- **`restrictOn` is supported in `S`**: the edge support of `restrictOn S n` is a
subset of `S`, since off `S` the restriction vanishes. Part of ingredient
**SL-D₁** brick D1b foundation. -/
theorem Current.support_restrictOn_subset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) :
    (n.restrictOn G Λ S).support G Λ ⊆ S := by
  classical
  intro e he
  simp only [Current.support, Finset.mem_filter, Finset.mem_univ, true_and] at he
  by_contra hS
  exact he (Current.restrictOn_apply_not_mem G Λ S n hS)

omit [DecidableEq V] in
/-- **Block-weight invariance of `restrictOn`**: the FV (3.45) block factor over
`S` reads only `n|_S`, so `restrictOn S n` and `n` give the same block product
`∏_{e ∈ S} (βJ)^{n_e}/n_e!`. Part of ingredient **SL-D₁** brick D1b foundation;
weight source FV (3.45). -/
theorem Current.prod_factor_restrictOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (β J : ℝ)
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) :
    (∏ e ∈ S, (β * J) ^ ((n.restrictOn G Λ S) e)
        / (((n.restrictOn G Λ S) e).factorial : ℝ))
      = ∏ e ∈ S, (β * J) ^ (n e) / ((n e).factorial : ℝ) := by
  refine Finset.prod_congr rfl (fun e he => ?_)
  rw [Current.restrictOn_apply_mem G Λ S n he]

omit [DecidableEq V] in
/-- **`degreeOn` invariance of `restrictOn`**: the `S`-restricted incident degree
reads only `n|_S`, so `degreeOn S (restrictOn S n) v = degreeOn S n v`. Part of
ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.degreeOn_restrictOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) :
    (n.restrictOn G Λ S).degreeOn G Λ S v = n.degreeOn G Λ S v := by
  unfold Current.degreeOn
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Current.restrictOn_apply_mem G Λ S n he]

omit [DecidableEq V] in
/-- **`parityOn` invariance of `restrictOn`**: the mod-2 restricted parity reads
only `n|_S`, so `parityOn S (restrictOn S n) v = parityOn S n v` (mod-2 cast of
`degreeOn_restrictOn`). Part of ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.parityOn_restrictOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) :
    (n.restrictOn G Λ S).parityOn G Λ S v = n.parityOn G Λ S v := by
  rw [Current.parityOn_eq_degreeOn, Current.parityOn_eq_degreeOn,
    Current.degreeOn_restrictOn]

omit [DecidableEq V] in
/-- **`sourcesOn` invariance of `restrictOn`**: the `S`-restricted source set reads
only `n|_S`, so `sourcesOn S (restrictOn S n) = sourcesOn S n` (filter through
`parityOn_restrictOn`). Part of ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.sourcesOn_restrictOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) :
    (n.restrictOn G Λ S).sourcesOn G Λ S = n.sourcesOn G Λ S := by
  ext v
  rw [Current.mem_sourcesOn_iff, Current.mem_sourcesOn_iff,
    Current.parityOn_restrictOn]

omit [DecidableEq V] in
/-- **Every induced-graph edge has exactly two incident vertices**: the count of
`v : ↑Λ` lying on a fixed edge `e` of the induced graph is `2` (an edge is a
non-diagonal `Sym2 ↑Λ`). This is the per-edge input to the handshaking identity.
Part of ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.card_incident_eq_two (G : SimpleGraph V) (Λ : Finset V)
    [DecidableEq ↑Λ]
    (e : (inducedGraph G Λ).edgeSet) :
    (Finset.univ.filter (fun v : ↑Λ => v ∈ (e : Sym2 ↑Λ))).card = 2 := by
  have hfilter :
      Finset.univ.filter (fun v : ↑Λ => v ∈ (e : Sym2 ↑Λ))
        = (e : Sym2 ↑Λ).toFinset := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_toFinset]
  rw [hfilter]
  refine Sym2.card_toFinset_of_not_isDiag _ ?_
  exact SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2

omit [DecidableEq V] in
/-- **Even-cardinality (handshaking) identity for the restricted degree**: summing
the `S`-restricted incident degree over all vertices double-counts each edge of
`S`, giving `∑_v degreeOn S n v = 2 · ∑_{e ∈ S} n e` (each edge contributes to its
exactly two endpoints). This is the clean `Finset.sum` parity helper of D1b item 2.
Part of ingredient **SL-D₁** brick D1b foundation. -/
theorem Current.degreeOn_sum_eq_two_mul (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) :
    (∑ v : ↑Λ, n.degreeOn G Λ S v) = 2 * ∑ e ∈ S, n e := by
  unfold Current.degreeOn
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, Current.card_incident_eq_two G Λ e,
    smul_eq_mul, Nat.mul_comm]

omit [DecidableEq V] in
/-- **The restricted source set has even cardinality** (handshaking corollary).
The `S`-restricted source set `sourcesOn S n` (vertices of odd `S`-degree) has even
cardinality, because `∑_v degreeOn S n v` is even (`degreeOn_sum_eq_two_mul`) and
the number of odd-degree vertices has the parity of the degree sum.

*This does not establish any nondegeneracy `x ≠ a`, and the corrected D1b design
no longer needs it.* Evenness of the source cardinality is consistent with
`sourcesOn (interiorEdges C) M = ∅` (the `x = a` degenerate branch), so it cannot
rule out `x = a`; the resolved design handles that branch via the
symmetric-difference source form `{x} △ {a}`
(`Current.pivotalFiber_sourcesOn_symmDiff`), see the module docstring. This lemma is
kept as a true auxiliary but is off the D1b critical path. Part of ingredient
**SL-D₁** brick D1b foundation. -/
theorem Current.sourcesOn_card_even (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) :
    Even (n.sourcesOn G Λ S).card := by
  classical
  -- The mod-2 sum of restricted parities equals the source cardinality, and also
  -- equals the mod-2 cast of the (even) degree sum, hence the cardinality is even.
  have hpar : ∀ v : ↑Λ,
      n.parityOn G Λ S v = (if n.parityOn G Λ S v ≠ 0 then (1 : ZMod 2) else 0) := by
    intro v
    by_cases h : n.parityOn G Λ S v = 0
    · simp [h]
    · rw [if_pos h]
      revert h
      generalize n.parityOn G Λ S v = a
      revert a
      decide
  have e1 : (∑ v : ↑Λ, n.parityOn G Λ S v)
      = ((n.sourcesOn G Λ S).card : ZMod 2) := by
    calc (∑ v : ↑Λ, n.parityOn G Λ S v)
        = ∑ v : ↑Λ, (if n.parityOn G Λ S v ≠ 0 then (1 : ZMod 2) else 0) := by
          exact Finset.sum_congr rfl (fun v _ => hpar v)
      _ = ((Finset.univ.filter (fun v => n.parityOn G Λ S v ≠ 0)).card : ZMod 2) :=
          Finset.sum_boole _ _
      _ = ((n.sourcesOn G Λ S).card : ZMod 2) := by rw [Current.sourcesOn]
  have e2 : (∑ v : ↑Λ, n.parityOn G Λ S v) = 0 := by
    have hcast : ∀ v : ↑Λ,
        n.parityOn G Λ S v = ((n.degreeOn G Λ S v : ℕ) : ZMod 2) :=
      fun v => Current.parityOn_eq_degreeOn G Λ S n v
    simp_rw [hcast]
    rw [← Nat.cast_sum, Current.degreeOn_sum_eq_two_mul, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]
  rw [← ZMod.natCast_eq_zero_iff_even, ← e1, e2]

end Ambient

end IsingModel
