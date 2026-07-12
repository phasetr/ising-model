import IsingModel.Inequalities.ClusterConditioningFiberDecouple
import IsingModel.Inequalities.ClusterConditioningPivotal
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# SL-D brick D1b part 2b: the gluing bijection `Φ` and the weight-level `tsum` Fubini

This module implements **ingredient SL-D, brick D1b part 2b** — the
**completion of `SL-D₁` (range independence)**
(`.self-local/tex/rc-oz-lemma51-SLD1b-part2.tex`, §③/④). Building on the part 2a
decoupling foundation (`Current.reachableCluster_confined_eq`,
`Current.sources_eq_sourcesOn_of_supported`,
`Current.summable_block_weight_if_sourcesOn`) it delivers the restriction/gluing
bijection between the pinned pivotal fiber and the product of the interior/exterior
block ensembles, and the resulting weight-level `tsum` Fubini
\[
  \Sigma_C \;=\; (\beta J)\cdot \Xi_{\mathrm{int}}\cdot \Xi_{\mathrm{ext}} .
\]

## Contents

* `Current.pivotalFiberSet`, `Current.interiorBlockSet`, `Current.exteriorBlockSet` —
  the pinned pivotal fiber `𝓕_C` and the interior/exterior block ensembles
  `𝒜_int`/`𝒜_ext`, all as subsets of the single ambient current type
  `Current G Λ = E → ℕ` (symmetric-difference source constraints `{x} △ {a}`,
  `{b} △ {y}`, part 1 correction). `𝒜_ext` is an **ambient** block weight sum; no
  subgraph current is ever formed.
* `Current.glueBlocks` — the gluing map `Ψ`, realised as the ambient sum
  `n_int + n_ext + 1_{e₀}` (equal, on block-supported inputs, to the piecewise glue
  that is `n_int` on `E_int`, `n_ext` on `E_ext`, `1` on the bridge `e₀`, and `0`
  on the remaining crossing edges).
* `Current.pivotalFiberEquiv` — the SL-D₁ range-independence **bijection**
  `Φ : 𝓕_C ≃ 𝒜_int × 𝒜_ext`, `Φ(M) = (M|_{E_int}, M|_{E_ext})`, with inverse the
  gluing `Ψ`. Its round-trips are per-edge `funext` case splits plus F2/F3 pinning;
  the reverse `EdgePivotal` reconstruction concatenates the three legs
  `x ⤳ a` / `a — b` / `b ⤳ y` and uses the part 2a confinement lemma for the
  non-reachability clause, and the D1a `ZMod 2` parity split for `sources = {x, y}`.
* `Current.pivotalNumerator_fiber_factor` — the headline **weight-level `tsum`
  Fubini** `Σ_C = (βJ)·Ξ_int·Ξ_ext`, proved by reindexing along `Φ`
  (`Equiv.tsum_eq`), the SL-C pointwise weight factorisation
  (`Current.weight_pivotal_fiber_factor`), and the product split
  `Summable.tsum_mul_tsum` fed by the part 2a block-summability lemma.

## Honest status: D1b part 2b = SL-D₁ complete, but Lemma 5.1 is NOT complete

D1b part 2b **completes `SL-D₁` (range independence)**: together with D1a, part 1
and part 2a it establishes the weight-level factorisation of the pinned pivotal
fiber sum with `Ξ_int`, `Ξ_ext` **ambient** block weight sums. It is an explicitly
**tracked ingredient** (Group 1a, SL-D₁), on the downstream path to the (future)
Lemma 5.1 → P2-ii → `hLogLip` → the lower-semicontinuity half of GJ Theorem 17.5.1
(§17.5, issue #4386 / thread #4418).

It introduces **no** subgraph current, **no** switching lemma, and **no**
identification of `Ξ_ext` with a two-point function. Therefore **the SL-D₂ core**
(the exterior → two-point collapse: conditioned-switching / subgraph-conditioning,
Aizenman Lemma 4.1) **awaits explicit user authorisation** and remains the gate:
**SL-D₁ completion does not complete Lemma 5.1** (SL-D₂ gates it). This module
touches none of SL-D₂; it stays reference-count zero into the live capstone. The
weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current weight of
Friedli–Velenik, eq. (3.45).

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7, eq. (3.45).
* Glimm–Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.5.1, p. 312 (lsc half,
  issue #4386 / thread #4418).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/

namespace IsingModel

namespace Ambient

open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **`ZMod 2` indicator of a singleton symmetric difference**: for points `p, q, v`
of a `DecidableEq` type, `[v ∈ {p} △ {q}] = [v = p] + [v = q]` in `ZMod 2`. The
`ZMod 2` inversion behind the D1a source split, reused here to compute the parity of
the glued current. Part of ingredient **SL-D₁** brick D1b part 2b. -/
theorem zmod2_ite_singleton_symmDiff {α : Type*} [DecidableEq α] (p q v : α) :
    (if v ∈ ({p} : Finset α) ∆ {q} then (1 : ZMod 2) else 0)
      = (if v = p then 1 else 0) + (if v = q then 1 else 0) := by
  simp only [Finset.mem_symmDiff, Finset.mem_singleton]
  split_ifs with h1 h2 h3 <;> first | decide | (exfalso; tauto)

variable (G : SimpleGraph V) (Λ : Finset V)
  [Fintype (inducedGraph G Λ).edgeSet]

/-- **`restrictOn` is idempotent**: restricting twice to the same edge subset `S`
equals restricting once, `(restrictOn S n)|_S = restrictOn S n`. Off `S` both sides
vanish; on `S` both read `n`. Part of ingredient **SL-D₁** brick D1b part 2b
(needed to certify that a block restriction lies in its block ensemble). -/
theorem Current.restrictOn_idem (S : Finset (inducedGraph G Λ).edgeSet)
    (n : Current G Λ) :
    (n.restrictOn G Λ S).restrictOn G Λ S = n.restrictOn G Λ S := by
  funext e
  by_cases he : e ∈ S
  · rw [Current.restrictOn_apply_mem G Λ S (n.restrictOn G Λ S) he]
  · rw [Current.restrictOn_apply_not_mem G Λ S (n.restrictOn G Λ S) he,
      Current.restrictOn_apply_not_mem G Λ S n he]

/-- **The pinned pivotal fiber `𝓕_C`** (part 2b, spec `def:blocks` ambient fiber).
The set of ambient currents `M : Current G Λ` that are pivotal for `x, y` through the
dominant edge `e₀`, have global source set `{x, y}`, and decremented cluster value
`reachableCluster (M − 1_{e₀}) x = C`. Its weight sum is the fiber numerator `Σ_C`.
Part of ingredient **SL-D₁** brick D1b part 2b (tracked ingredient, Group 1a; SL-D₂
awaits explicit user authorisation); weight source FV (3.45). -/
def Current.pivotalFiberSet (e₀ : (inducedGraph G Λ).edgeSet) (C : Finset ↑Λ)
    (x y : ↑Λ) : Set (Current G Λ) :=
  {M | Current.EdgePivotal G Λ e₀ M x y ∧ M.sources G Λ = {x, y} ∧
    Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C}

/-- **The interior block ensemble `𝒜_int(C, x, a)`** (part 2b, spec `def:blocks`).
The set of ambient currents `n` supported in the interior edge block
`interiorEdges C` (`restrictOn (interiorEdges C) n = n`), with interior source set
the symmetric difference `{x} △ {a}` and reachable cluster
`reachableCluster n x = C`. Its ambient block weight sum is `Ξ_int`. Part of
ingredient **SL-D₁** brick D1b part 2b (tracked ingredient, Group 1a; SL-D₂ awaits
explicit user authorisation); weight source FV (3.45). -/
def Current.interiorBlockSet (C : Finset ↑Λ) (x a : ↑Λ) : Set (Current G Λ) :=
  {n | n.restrictOn G Λ (Current.interiorEdges G Λ C) = n ∧
    n.sourcesOn G Λ (Current.interiorEdges G Λ C) = ({x} : Finset ↑Λ) ∆ {a} ∧
    Current.reachableCluster G Λ n x = C}

/-- **The exterior block ensemble `𝒜_ext(C, b, y)`** (part 2b, spec `def:blocks`).
The set of ambient currents `n` supported in the exterior edge block
`interiorEdges Cᶜ` (`restrictOn (interiorEdges Cᶜ) n = n`), with exterior source set
the symmetric difference `{b} △ {y}`. **No** cluster constraint and, crucially, **no**
identification with a two-point function: `𝒜_ext` stays an *ambient* block weight sum
(the SL-D₂ collapse awaits explicit user authorisation). Its ambient block weight sum
is `Ξ_ext`. Part of ingredient **SL-D₁** brick D1b part 2b (tracked ingredient,
Group 1a; SL-D₂ awaits explicit user authorisation); weight source FV (3.45). -/
def Current.exteriorBlockSet (C : Finset ↑Λ) (b y : ↑Λ) : Set (Current G Λ) :=
  {n | n.restrictOn G Λ (Current.interiorEdges G Λ Cᶜ) = n ∧
    n.sourcesOn G Λ (Current.interiorEdges G Λ Cᶜ) = ({b} : Finset ↑Λ) ∆ {y}}

/-- **The gluing map `Ψ`** (part 2b, spec `prop:phi`). Glues an interior block
current `n_int` and an exterior block current `n_ext` across the pinned bridge `e₀`,
realised as the ambient sum `n_int + n_ext + 1_{e₀}`
(`1_{e₀} = fromEdgeFinset {e₀}`). On block-supported inputs
(`n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`) this equals the piecewise glue that is `n_int` on
`E_int`, `n_ext` on `E_ext`, `1` on the bridge `e₀`, and `0` on the remaining
crossing edges (the two blocks and `{e₀}` occupy disjoint edges, so the sum reads off
one summand per edge). Part of ingredient **SL-D₁** brick D1b part 2b (tracked
ingredient, Group 1a; SL-D₂ awaits explicit user authorisation);
weight source FV (3.45). -/
def Current.glueBlocks (e₀ : (inducedGraph G Λ).edgeSet)
    (n_int n_ext : Current G Λ) : Current G Λ :=
  n_int + n_ext + Current.fromEdgeFinset G Λ {e₀}

/-- **The glue minus its bridge is the pure block sum**:
`glueBlocks e₀ n_int n_ext − 1_{e₀} = n_int + n_ext`. Pointwise the bridge summand
`1_{e₀}` cancels under truncated subtraction. This is the current `M − 1_{e₀}` used in
the reverse `EdgePivotal` non-reachability clause. Part of ingredient **SL-D₁** brick
D1b part 2b. -/
theorem Current.glueBlocks_sub_dominant (e₀ : (inducedGraph G Λ).edgeSet)
    (n_int n_ext : Current G Λ) :
    Current.glueBlocks G Λ e₀ n_int n_ext - Current.fromEdgeFinset G Λ {e₀}
      = n_int + n_ext := by
  funext e
  simp only [Current.glueBlocks, Current.sub_apply, Current.add_apply]
  omega

/-- **Pointwise value of the singleton indicator current**:
`fromEdgeFinset {e₀} e = if e = e₀ then 1 else 0`. Part of ingredient **SL-D₁** brick
D1b part 2b. -/
theorem Current.fromEdgeFinset_singleton_apply (e₀ e : (inducedGraph G Λ).edgeSet) :
    Current.fromEdgeFinset G Λ {e₀} e = if e = e₀ then 1 else 0 := by
  simp only [Current.fromEdgeFinset, Finset.mem_singleton]

set_option linter.unusedDecidableInType false in
/-- **`e₀` is not an interior edge** (F1: `b ∉ C` escapes `C`). Part of ingredient
**SL-D₁** brick D1b part 2b. -/
theorem Current.dominant_not_mem_interiorEdges (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (hbC : b ∉ C) :
    e₀ ∉ Current.interiorEdges G Λ C := by
  rw [Current.mem_interiorEdges_iff]; push Not
  exact ⟨b, by rw [hab]; exact Sym2.mem_mk_right a b, hbC⟩

/-- **`e₀` is not an exterior edge** (F1: `a ∈ C` stays in `C`). Part of ingredient
**SL-D₁** brick D1b part 2b. -/
theorem Current.dominant_not_mem_interiorEdges_compl (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (haC : a ∈ C) :
    e₀ ∉ Current.interiorEdges G Λ Cᶜ := by
  rw [Current.mem_interiorEdges_iff]; push Not
  exact ⟨a, by rw [hab]; exact Sym2.mem_mk_left a b,
    fun h => (Finset.mem_compl.mp h) haC⟩

set_option linter.unusedDecidableInType false in
/-- **`Φ` lands in `𝒜_int`** (forward interior landing, part 2b §① + confinement).
For `M` in the pinned pivotal fiber, its interior restriction
`M|_{E_int} = restrictOn (interiorEdges C) M` lies in the interior block ensemble
`𝒜_int(C, x, a)`: it is block-supported (`restrictOn_idem`), has interior source set
`{x} △ {a}` (`sourcesOn_restrictOn` + D1b part 1 `pivotalFiber_sourcesOn_symmDiff`),
and reachable cluster `C` by the part 2a interior-confinement lemma
`reachableCluster_confined_eq`. Part of ingredient **SL-D₁** brick D1b part 2b
(tracked ingredient, Group 1a; SL-D₂ awaits explicit user authorisation);
weight source FV (3.45). -/
theorem Current.restrictOn_mem_interiorBlockSet (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (M : Current G Λ)
    (hM : M ∈ Current.pivotalFiberSet G Λ e₀ C x y) :
    M.restrictOn G Λ (Current.interiorEdges G Λ C)
      ∈ Current.interiorBlockSet G Λ C x a := by
  obtain ⟨hpiv, hsrc, hC⟩ := hM
  refine ⟨Current.restrictOn_idem G Λ _ M, ?_, ?_⟩
  · rw [Current.sourcesOn_restrictOn G Λ _ M]
    exact (Current.pivotalFiber_sourcesOn_symmDiff G Λ e₀ M x y a b C hab hpiv hC
      haC hbC hsrc).1
  · refine Current.reachableCluster_confined_eq G Λ
      (M.restrictOn G Λ (Current.interiorEdges G Λ C))
      (M - Current.fromEdgeFinset G Λ {e₀}) C x ?_ ?_ hC ?_
    · intro e
      by_cases he : e ∈ Current.interiorEdges G Λ C
      · rw [Current.restrictOn_apply_mem G Λ _ M he, Current.sub_apply]
        have he0 : e ≠ e₀ := fun h =>
          Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC (h ▸ he)
        simp only [Current.fromEdgeFinset, Finset.mem_singleton, if_neg he0]
        omega
      · rw [Current.restrictOn_apply_not_mem G Λ _ M he]; exact Nat.zero_le _
    · intro e he
      rw [Current.restrictOn_apply_mem G Λ _ M he, Current.sub_apply,
        Current.fromEdgeFinset_singleton_apply]
      have he0 : e ≠ e₀ := fun h =>
        Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC (h ▸ he)
      rw [if_neg he0]; omega
    · intro e he hinc
      by_contra heInt
      rw [Current.mem_interiorEdges_iff] at heInt
      push Not at heInt
      obtain ⟨w', hw'e, hw'C⟩ := heInt
      obtain ⟨w, hwe, hwC⟩ := hinc
      have hwne : w ≠ w' := fun h => hw'C (h ▸ hwC)
      have hesym : (e : Sym2 ↑Λ) = s(w, w') :=
        (Sym2.mem_and_mem_iff hwne).mp ⟨hwe, hw'e⟩
      have he0 : e ≠ e₀ := by
        intro heq
        have hMe0 : M e₀ = 1 :=
          Current.edgePivotal_dominant_edge_eq_one G Λ e₀ M x y a b hab hpiv
        rw [Current.mem_support_iff, Current.sub_apply, heq, hMe0,
          Current.fromEdgeFinset_singleton_apply, if_pos rfl] at he
        omega
      have hwmem : w ∈ Current.reachableCluster G Λ
          (M - Current.fromEdgeFinset G Λ {e₀}) x := by rw [hC]; exact hwC
      have hw'nmem : w' ∉ Current.reachableCluster G Λ
          (M - Current.fromEdgeFinset G Λ {e₀}) x := by rw [hC]; exact hw'C
      have hMe : M e = 0 :=
        Current.edgePivotal_no_spectator_crossing G Λ e₀ e M x w w'
          hwmem hw'nmem hesym he0
      rw [Current.mem_support_iff, Current.sub_apply,
        Current.fromEdgeFinset_singleton_apply, if_neg he0, hMe] at he
      omega

set_option linter.unusedDecidableInType false in
/-- **`Φ` lands in `𝒜_ext`** (forward exterior landing, part 2b §①). For `M` in the
pinned pivotal fiber, its exterior restriction `M|_{E_ext}` lies in the exterior
block ensemble `𝒜_ext(C, b, y)`: block-supported (`restrictOn_idem`), with exterior
source set `{b} △ {y}` (`sourcesOn_restrictOn` + `pivotalFiber_sourcesOn_symmDiff`).
No cluster constraint (exterior side). Part of ingredient **SL-D₁** brick D1b part 2b
(tracked ingredient, Group 1a; SL-D₂ awaits explicit user authorisation);
weight source FV (3.45). -/
theorem Current.restrictOn_mem_exteriorBlockSet (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (M : Current G Λ)
    (hM : M ∈ Current.pivotalFiberSet G Λ e₀ C x y) :
    M.restrictOn G Λ (Current.interiorEdges G Λ Cᶜ)
      ∈ Current.exteriorBlockSet G Λ C b y := by
  obtain ⟨hpiv, hsrc, hC⟩ := hM
  refine ⟨Current.restrictOn_idem G Λ _ M, ?_⟩
  rw [Current.sourcesOn_restrictOn G Λ _ M]
  exact (Current.pivotalFiber_sourcesOn_symmDiff G Λ e₀ M x y a b C hab hpiv hC
    haC hbC hsrc).2

set_option linter.unusedDecidableInType false in
/-- **`Ψ ∘ Φ = id`** (round-trip, part 2b §③(a), pinning). For `M` in the pinned
pivotal fiber, gluing back its interior and exterior restrictions recovers `M`:
`glueBlocks e₀ (M|_{E_int}) (M|_{E_ext}) = M`. A per-edge `funext`: on `E_int`/`E_ext`
the corresponding restriction reads `M`; on the bridge `e₀` the glue is `1 = M e₀`
(F2, `edgePivotal_dominant_edge_eq_one`); on the remaining crossing edges the glue is
`0 = M e` (F3, `edgePivotal_no_spectator_crossing`). Part of ingredient **SL-D₁**
brick D1b part 2b (tracked ingredient, Group 1a; SL-D₂ awaits explicit user
authorisation); weight source FV (3.45). -/
theorem Current.glueBlocks_restrictOn (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (M : Current G Λ)
    (hM : M ∈ Current.pivotalFiberSet G Λ e₀ C x y) :
    Current.glueBlocks G Λ e₀ (M.restrictOn G Λ (Current.interiorEdges G Λ C))
      (M.restrictOn G Λ (Current.interiorEdges G Λ Cᶜ)) = M := by
  obtain ⟨hpiv, _, hC⟩ := hM
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_int := Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC
  have he0_ext := Current.dominant_not_mem_interiorEdges_compl G Λ e₀ C a b hab haC
  funext e
  simp only [Current.glueBlocks, Current.add_apply,
    Current.fromEdgeFinset_singleton_apply]
  by_cases heInt : e ∈ Current.interiorEdges G Λ C
  · have h1 := Current.restrictOn_apply_mem G Λ (Current.interiorEdges G Λ C) M heInt
    have h2 := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ Cᶜ) M
      (Finset.disjoint_left.mp hdisj heInt)
    have he0 : e ≠ e₀ := fun h => he0_int (h ▸ heInt)
    rw [if_neg he0]; omega
  · by_cases heExt : e ∈ Current.interiorEdges G Λ Cᶜ
    · have h1 := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ C) M heInt
      have h2 := Current.restrictOn_apply_mem G Λ (Current.interiorEdges G Λ Cᶜ) M heExt
      have he0 : e ≠ e₀ := fun h => he0_ext (h ▸ heExt)
      rw [if_neg he0]; omega
    · have h1 := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ C) M heInt
      have h2 := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ Cᶜ) M heExt
      by_cases he0 : e = e₀
      · have hMe0 : M e₀ = 1 :=
          Current.edgePivotal_dominant_edge_eq_one G Λ e₀ M x y a b hab hpiv
        have hMe : M e = 1 := he0.symm ▸ hMe0
        rw [if_pos he0]; omega
      · rw [Current.mem_interiorEdges_iff] at heInt heExt
        push Not at heInt heExt
        obtain ⟨w', hw'e, hw'C⟩ := heInt
        obtain ⟨w, hwe, hwCc⟩ := heExt
        have hwC : w ∈ C := by
          by_contra h; exact hwCc (Finset.mem_compl.mpr h)
        have hwne : w ≠ w' := fun h => hw'C (h ▸ hwC)
        have hesym : (e : Sym2 ↑Λ) = s(w, w') :=
          (Sym2.mem_and_mem_iff hwne).mp ⟨hwe, hw'e⟩
        have hwmem : w ∈ Current.reachableCluster G Λ
            (M - Current.fromEdgeFinset G Λ {e₀}) x := by rw [hC]; exact hwC
        have hw'nmem : w' ∉ Current.reachableCluster G Λ
            (M - Current.fromEdgeFinset G Λ {e₀}) x := by rw [hC]; exact hw'C
        have hMe : M e = 0 :=
          Current.edgePivotal_no_spectator_crossing G Λ e₀ e M x w w'
            hwmem hw'nmem hesym he0
        rw [if_neg he0]; omega

set_option linter.unusedDecidableInType false in
/-- **`Φ ∘ Ψ = id` (interior component)** (round-trip, part 2b §③(a)). For block
currents `n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`, restricting the glue to `E_int` recovers
`n_int`: on `E_int` the glue reads `n_int` (the exterior and bridge summands vanish
there); off `E_int` both sides vanish (`n_int` is block-supported). Part of
ingredient **SL-D₁** brick D1b part 2b. -/
theorem Current.restrictOn_glueBlocks_interior (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (hbC : b ∉ C)
    (n_int n_ext : Current G Λ)
    (hint : n_int ∈ Current.interiorBlockSet G Λ C x a)
    (hext : n_ext ∈ Current.exteriorBlockSet G Λ C b y) :
    (Current.glueBlocks G Λ e₀ n_int n_ext).restrictOn G Λ
        (Current.interiorEdges G Λ C) = n_int := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_int := Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC
  funext e
  by_cases heInt : e ∈ Current.interiorEdges G Λ C
  · rw [Current.restrictOn_apply_mem G Λ _ _ heInt]
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hne : n_ext e = 0 := by
      have := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ Cᶜ)
        n_ext (Finset.disjoint_left.mp hdisj heInt)
      rwa [hext.1] at this
    have he0 : e ≠ e₀ := fun h => he0_int (h ▸ heInt)
    rw [if_neg he0]; omega
  · rw [Current.restrictOn_apply_not_mem G Λ _ _ heInt]
    have hz : n_int e = 0 := by
      have := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ C)
        n_int heInt
      rwa [hint.1] at this
    omega

set_option linter.unusedDecidableInType false in
/-- **`Φ ∘ Ψ = id` (exterior component)** (round-trip, part 2b §③(a)). For block
currents `n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`, restricting the glue to `E_ext` recovers
`n_ext`. Symmetric to the interior component. Part of ingredient **SL-D₁** brick
D1b part 2b. -/
theorem Current.restrictOn_glueBlocks_exterior (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (haC : a ∈ C)
    (n_int n_ext : Current G Λ)
    (hint : n_int ∈ Current.interiorBlockSet G Λ C x a)
    (hext : n_ext ∈ Current.exteriorBlockSet G Λ C b y) :
    (Current.glueBlocks G Λ e₀ n_int n_ext).restrictOn G Λ
        (Current.interiorEdges G Λ Cᶜ) = n_ext := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_ext := Current.dominant_not_mem_interiorEdges_compl G Λ e₀ C a b hab haC
  funext e
  by_cases heExt : e ∈ Current.interiorEdges G Λ Cᶜ
  · rw [Current.restrictOn_apply_mem G Λ _ _ heExt]
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hni : n_int e = 0 := by
      have := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ C)
        n_int (Finset.disjoint_right.mp hdisj heExt)
      rwa [hint.1] at this
    have he0 : e ≠ e₀ := fun h => he0_ext (h ▸ heExt)
    rw [if_neg he0]; omega
  · rw [Current.restrictOn_apply_not_mem G Λ _ _ heExt]
    have hz : n_ext e = 0 := by
      have := Current.restrictOn_apply_not_mem G Λ (Current.interiorEdges G Λ Cᶜ)
        n_ext heExt
      rwa [hext.1] at this
    omega

set_option linter.unusedDecidableInType false in
/-- **`Ψ` lands in `𝓕_C`** (reverse landing, part 2b §③(b)). For block currents
`n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`, the glue `M = glueBlocks e₀ n_int n_ext` lies in the
pinned pivotal fiber `𝓕_C`:

* **`EdgePivotal`** — `Reachable x y` in `M.toSimpleGraph` by concatenating the three
  legs `x ⤳ a` (through `n_int`, `a ∈ C = reachableCluster n_int x`),
  `a — b` (the pinned bridge `M e₀ = 1`), and `b ⤳ y` (through `n_ext`, global sources
  `{b} △ {y}`); and *non*-`Reachable x y` in `(M − 1_{e₀}).toSimpleGraph` because
  `M − 1_{e₀} = n_int + n_ext` is confined to `C` while `y ∉ C`.
* **`sources M = {x, y}`** — the `ZMod 2` parity of the glue splits as
  `[v ∈ {x} △ {a}] + [v ∈ {b} △ {y}] + [v ∈ e₀]`, which cancels the `a, b` bumps,
  leaving `[v = x] + [v = y]` (`x ∈ C`, `y ∉ C`, so `x ≠ y`).

Part of ingredient **SL-D₁** brick D1b part 2b (tracked ingredient, Group 1a; SL-D₂
awaits explicit user authorisation); weight source FV (3.45). -/
theorem Current.glueBlocks_mem_pivotalFiberSet (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (n_int n_ext : Current G Λ)
    (hint : n_int ∈ Current.interiorBlockSet G Λ C x a)
    (hext : n_ext ∈ Current.exteriorBlockSet G Λ C b y) :
    Current.glueBlocks G Λ e₀ n_int n_ext
      ∈ Current.pivotalFiberSet G Λ e₀ C x y := by
  obtain ⟨hni_r, hni_s, hni_c⟩ := hint
  obtain ⟨hne_r, hne_s⟩ := hext
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_int := Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC
  have he0_ext := Current.dominant_not_mem_interiorEdges_compl G Λ e₀ C a b hab haC
  have hab_ne : a ≠ b := by
    have hmem := e₀.2
    rw [hab, SimpleGraph.mem_edgeSet] at hmem
    exact hmem.ne
  have hni_off : ∀ e ∉ Current.interiorEdges G Λ C, n_int e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_int he
    rwa [hni_r] at this
  have hne_off : ∀ e ∉ Current.interiorEdges G Λ Cᶜ, n_ext e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_ext he
    rwa [hne_r] at this
  have hni_supp : n_int.support G Λ ⊆ Current.interiorEdges G Λ C := by
    intro e he
    rw [Current.mem_support_iff] at he
    by_contra h; exact he (hni_off e h)
  have hne_supp : n_ext.support G Λ ⊆ Current.interiorEdges G Λ Cᶜ := by
    intro e he
    rw [Current.mem_support_iff] at he
    by_contra h; exact he (hne_off e h)
  set M := Current.glueBlocks G Λ e₀ n_int n_ext with hMdef
  have hniM : n_int ≤ M := by
    intro e; simp only [hMdef, Current.glueBlocks, Current.add_apply]; omega
  have hneM : n_ext ≤ M := by
    intro e; simp only [hMdef, Current.glueBlocks, Current.add_apply]; omega
  have hxC : x ∈ C := by
    rw [← hni_c, Current.mem_reachableCluster_iff]
  have hyC : y ∉ C := by
    rcases eq_or_ne b y with hby | hby
    · rw [← hby]; exact hbC
    · have hy_mem : y ∈ n_ext.sourcesOn G Λ (Current.interiorEdges G Λ Cᶜ) := by
        rw [hne_s, Finset.mem_symmDiff]; right
        exact ⟨Finset.mem_singleton_self y,
          by simp only [Finset.mem_singleton]; exact fun h => hby h.symm⟩
      rw [Current.mem_sourcesOn_iff] at hy_mem
      intro hyC'
      rw [Current.parityOn_eq_degreeOn,
        Current.degreeOn_interiorEdges_compl_eq_zero_of_mem G Λ C n_ext y hyC'] at hy_mem
      simp at hy_mem
  have hxy : x ≠ y := fun h => hyC (h ▸ hxC)
  have hMe0 : M e₀ = 1 := by
    simp only [hMdef, Current.glueBlocks, Current.add_apply,
      hni_off e₀ he0_int, hne_off e₀ he0_ext]
    simp [Current.fromEdgeFinset]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have hxa : (n_int.toSimpleGraph G Λ).Reachable x a := by
      rw [← Current.mem_reachableCluster_iff, hni_c]; exact haC
    have hxa_M : (M.toSimpleGraph G Λ).Reachable x a :=
      hxa.mono (Current.toSimpleGraph_mono_of_le G Λ hniM)
    have hamem : a ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_left a b
    have hbmem : b ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_right a b
    have hAdjab : M.Adj G Λ a b :=
      ⟨hab_ne, e₀, (Current.mem_support_iff G Λ M e₀).mpr (by rw [hMe0]; omega),
        hamem, hbmem⟩
    have hab_M : (M.toSimpleGraph G Λ).Reachable a b :=
      ((Current.toSimpleGraph_adj_iff G Λ M a b).mpr hAdjab).reachable
    have hby_M : (M.toSimpleGraph G Λ).Reachable b y := by
      rcases eq_or_ne b y with hby | hby
      · rw [hby]
      · have hsrc_ne : n_ext.sources G Λ = ({b} : Finset ↑Λ) ∆ {y} := by
          rw [Current.sources_eq_sourcesOn_of_supported G Λ _ n_ext hne_supp]
          exact hne_s
        have hpair : n_ext.sources G Λ = {b, y} := by
          rw [hsrc_ne]; ext v
          rw [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_singleton,
            Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩)
            · exact Or.inl h
            · exact Or.inr h
          · rintro (rfl | rfl)
            · exact Or.inl ⟨rfl, hby⟩
            · exact Or.inr ⟨rfl, hby.symm⟩
        have := Current.sources_reachable_of_sources_eq_pair G Λ n_ext hby hpair
        exact this.mono (Current.toSimpleGraph_mono_of_le G Λ hneM)
    exact (hxa_M.trans hab_M).trans hby_M
  · rw [hMdef, Current.glueBlocks_sub_dominant G Λ e₀ n_int n_ext]
    have hsubC : ∀ v : ↑Λ, ((n_int + n_ext).toSimpleGraph G Λ).Reachable x v → v ∈ C := by
      have key : ∀ u v : ↑Λ, ((n_int + n_ext).toSimpleGraph G Λ).Walk u v →
          u ∈ C → v ∈ C := by
        intro u v w
        induction w with
        | nil => exact id
        | @cons u mid v hadj q ih =>
            intro hu
            refine ih ?_
            rw [Current.toSimpleGraph_adj_iff] at hadj
            obtain ⟨_, e, he, hue, hmide⟩ := hadj
            have heActive : (n_int + n_ext) e ≠ 0 :=
              (Current.mem_support_iff G Λ (n_int + n_ext) e).mp he
            rw [Current.add_apply] at heActive
            by_cases heInt : e ∈ Current.interiorEdges G Λ C
            · rw [Current.mem_interiorEdges_iff] at heInt
              exact heInt mid hmide
            · have heExt : e ∈ Current.interiorEdges G Λ Cᶜ := by
                by_contra heExt
                exact heActive (by rw [hni_off e heInt, hne_off e heExt])
              rw [Current.mem_interiorEdges_iff] at heExt
              exact absurd hu (Finset.mem_compl.mp (heExt u hue))
      intro v hv
      obtain ⟨p⟩ := hv
      exact key x v p hxC
    intro hreach
    exact hyC (hsubC y hreach)
  · have hsrc_ni : n_int.sources G Λ = ({x} : Finset ↑Λ) ∆ {a} := by
      rw [Current.sources_eq_sourcesOn_of_supported G Λ _ n_int hni_supp]
      exact hni_s
    have hsrc_ne : n_ext.sources G Λ = ({b} : Finset ↑Λ) ∆ {y} := by
      rw [Current.sources_eq_sourcesOn_of_supported G Λ _ n_ext hne_supp]
      exact hne_s
    ext v
    rw [Current.mem_sources_iff]
    have hval : ∀ (n : Current G Λ) (p q : ↑Λ),
        n.sources G Λ = ({p} : Finset ↑Λ) ∆ {q} →
        n.parity G Λ v = (if v = p then (1 : ZMod 2) else 0) + (if v = q then 1 else 0) := by
      intro n p q hn
      have hchar : (n.parity G Λ v ≠ 0) ↔ v ∈ ({p} : Finset ↑Λ) ∆ {q} := by
        rw [← Current.mem_sources_iff, hn]
      have hstep : n.parity G Λ v = if v ∈ ({p} : Finset ↑Λ) ∆ {q} then 1 else 0 := by
        by_cases hm : v ∈ ({p} : Finset ↑Λ) ∆ {q}
        · rw [if_pos hm]
          have hne : n.parity G Λ v ≠ 0 := hchar.mpr hm
          revert hne; generalize n.parity G Λ v = t; revert t; decide
        · rw [if_neg hm]
          have hne : ¬ n.parity G Λ v ≠ 0 := fun h => hm (hchar.mp h)
          rwa [not_not] at hne
      rw [hstep, zmod2_ite_singleton_symmDiff]
    have hV1 := hval n_int x a hsrc_ni
    have hV2 := hval n_ext b y hsrc_ne
    have hVe0 : (if v ∈ (e₀ : Sym2 ↑Λ) then (1 : ZMod 2) else 0)
        = (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
      have hiff : (v ∈ (e₀ : Sym2 ↑Λ)) ↔ v ∈ ({a} : Finset ↑Λ) ∆ {b} := by
        rw [hab, Sym2.mem_iff, Finset.mem_symmDiff, Finset.mem_singleton,
          Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl)
          · exact Or.inl ⟨rfl, hab_ne⟩
          · exact Or.inr ⟨rfl, fun h => hab_ne h.symm⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact Or.inl h
          · exact Or.inr h
      rw [if_congr hiff rfl rfl, zmod2_ite_singleton_symmDiff]
    have hpar : M.parity G Λ v
        = (if v = x then (1 : ZMod 2) else 0) + (if v = y then 1 else 0) := by
      simp only [hMdef, Current.glueBlocks]
      rw [Current.add_parity, Current.add_parity,
        Current.fromEdgeFinset_singleton_parity, hV1, hV2, hVe0]
      generalize (if v = x then (1 : ZMod 2) else 0) = tx
      generalize (if v = a then (1 : ZMod 2) else 0) = ta
      generalize (if v = b then (1 : ZMod 2) else 0) = tb
      generalize (if v = y then (1 : ZMod 2) else 0) = ty
      revert tx ta tb ty; decide
    rw [hpar, Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne v x with hx | hx
    · rw [if_pos hx, if_neg (fun h : v = y => hxy (hx ▸ h))]
      exact ⟨fun _ => Or.inl hx, fun _ => by decide⟩
    · rcases eq_or_ne v y with hy | hy
      · rw [if_neg hx, if_pos hy]
        exact ⟨fun _ => Or.inr hy, fun _ => by decide⟩
      · rw [if_neg hx, if_neg hy]
        exact ⟨fun h => absurd (by decide : (0 : ZMod 2) + 0 = 0) h,
          fun h => h.elim (fun h1 => absurd h1 hx) (fun h2 => absurd h2 hy)⟩
  · rw [hMdef, Current.glueBlocks_sub_dominant G Λ e₀ n_int n_ext]
    refine Finset.Subset.antisymm ?_ ?_
    · intro v hv
      rw [Current.mem_reachableCluster_iff] at hv
      have key : ∀ u w : ↑Λ, ((n_int + n_ext).toSimpleGraph G Λ).Walk u w →
          u ∈ C → w ∈ C := by
        intro u w wk
        induction wk with
        | nil => exact id
        | @cons u mid w hadj q ih =>
            intro hu
            refine ih ?_
            rw [Current.toSimpleGraph_adj_iff] at hadj
            obtain ⟨_, e, he, hue, hmide⟩ := hadj
            have heActive : (n_int + n_ext) e ≠ 0 :=
              (Current.mem_support_iff G Λ (n_int + n_ext) e).mp he
            rw [Current.add_apply] at heActive
            by_cases heInt : e ∈ Current.interiorEdges G Λ C
            · rw [Current.mem_interiorEdges_iff] at heInt
              exact heInt mid hmide
            · have heExt : e ∈ Current.interiorEdges G Λ Cᶜ := by
                by_contra heExt
                exact heActive (by rw [hni_off e heInt, hne_off e heExt])
              rw [Current.mem_interiorEdges_iff] at heExt
              exact absurd hu (Finset.mem_compl.mp (heExt u hue))
      obtain ⟨p⟩ := hv
      exact key x v p hxC
    · intro v hv
      rw [← hni_c] at hv
      rw [Current.mem_reachableCluster_iff] at hv ⊢
      have hni_le : n_int ≤ n_int + n_ext := fun e => by
        rw [Current.add_apply]; exact Nat.le_add_right _ _
      exact hv.mono (Current.toSimpleGraph_mono_of_le G Λ hni_le)

set_option linter.unusedDecidableInType false in
/-- **SL-D₁ range-independence bijection `Φ`** (part 2b, spec `prop:phi`). The map
`Φ : 𝓕_C ≃ 𝒜_int(C, x, a) × 𝒜_ext(C, b, y)`, `Φ(M) = (M|_{E_int}, M|_{E_ext})`, with
inverse the gluing `Ψ`. This is the combinatorial heart of `SL-D₁`: the pinned
pivotal fiber factorises as a product of the interior and exterior block ensembles,
on the single ambient current type (no subgraph current). Round-trips are
`glueBlocks_restrictOn` (left) and `restrictOn_glueBlocks_interior`/`_exterior`
(right); landing is `restrictOn_mem_interiorBlockSet`/`_exteriorBlockSet` (forward)
and `glueBlocks_mem_pivotalFiberSet` (reverse). Part of ingredient **SL-D₁** brick
D1b part 2b (tracked ingredient, Group 1a; SL-D₂ awaits explicit user
authorisation); weight source FV (3.45). -/
noncomputable def Current.pivotalFiberEquiv (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) :
    ↥(Current.pivotalFiberSet G Λ e₀ C x y) ≃
      ↥(Current.interiorBlockSet G Λ C x a)
        × ↥(Current.exteriorBlockSet G Λ C b y) where
  toFun M :=
    (⟨M.1.restrictOn G Λ (Current.interiorEdges G Λ C),
        Current.restrictOn_mem_interiorBlockSet G Λ e₀ C x y a b hab haC hbC M.1 M.2⟩,
     ⟨M.1.restrictOn G Λ (Current.interiorEdges G Λ Cᶜ),
        Current.restrictOn_mem_exteriorBlockSet G Λ e₀ C x y a b hab haC hbC M.1 M.2⟩)
  invFun p :=
    ⟨Current.glueBlocks G Λ e₀ p.1.1 p.2.1,
      Current.glueBlocks_mem_pivotalFiberSet G Λ e₀ C x y a b hab haC hbC
        p.1.1 p.2.1 p.1.2 p.2.2⟩
  left_inv := by
    rintro ⟨M, hM⟩
    exact Subtype.ext
      (Current.glueBlocks_restrictOn G Λ e₀ C x y a b hab haC hbC M hM)
  right_inv := by
    rintro ⟨⟨ni, hni⟩, ⟨ne, hne⟩⟩
    refine Prod.ext_iff.mpr ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · exact Current.restrictOn_glueBlocks_interior G Λ e₀ C x y a b hab hbC
        ni ne hni hne
    · exact Current.restrictOn_glueBlocks_exterior G Λ e₀ C x y a b hab haC
        ni ne hni hne

set_option linter.unusedDecidableInType false in
/-- **Pointwise weight factorisation of the glue** (part 2b §④ weight preservation).
For block currents `n_int ∈ 𝒜_int`, `n_ext ∈ 𝒜_ext`, the FV (3.45) weight of the glue
factors as `weight (glueBlocks e₀ n_int n_ext) = (βJ)·w_int(n_int)·w_ext(n_ext)`, with
`w_int`/`w_ext` the interior/exterior block products. Proof: the glue is in the pinned
pivotal fiber (`glueBlocks_mem_pivotalFiberSet`), so the SL-C fiber factorisation
`weight_pivotal_fiber_factor` applies; on `E_int` (resp. `E_ext`) the glue reads
`n_int` (resp. `n_ext`). Part of ingredient **SL-D₁** brick D1b part 2b;
weight source FV (3.45). -/
theorem Current.weight_glueBlocks_factor (β J : ℝ) (e₀ : (inducedGraph G Λ).edgeSet)
    (C : Finset ↑Λ) (x y a b : ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (haC : a ∈ C) (hbC : b ∉ C) (n_int n_ext : Current G Λ)
    (hint : n_int ∈ Current.interiorBlockSet G Λ C x a)
    (hext : n_ext ∈ Current.exteriorBlockSet G Λ C b y) :
    (Current.glueBlocks G Λ e₀ n_int n_ext).weight G Λ β J
      = (β * J)
        * (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (n_int e) / ((n_int e).factorial : ℝ))
        * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
            (β * J) ^ (n_ext e) / ((n_ext e).factorial : ℝ) := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have he0_int := Current.dominant_not_mem_interiorEdges G Λ e₀ C a b hab hbC
  have he0_ext := Current.dominant_not_mem_interiorEdges_compl G Λ e₀ C a b hab haC
  have hni_r := hint.1
  have hne_r := hext.1
  have hni_off : ∀ e ∉ Current.interiorEdges G Λ C, n_int e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_int he
    rwa [hni_r] at this
  have hne_off : ∀ e ∉ Current.interiorEdges G Λ Cᶜ, n_ext e = 0 := by
    intro e he
    have := Current.restrictOn_apply_not_mem G Λ _ n_ext he
    rwa [hne_r] at this
  obtain ⟨hpiv, _, hC⟩ := Current.glueBlocks_mem_pivotalFiberSet G Λ e₀ C x y a b
    hab haC hbC n_int n_ext hint hext
  have hg_int : ∀ e ∈ Current.interiorEdges G Λ C,
      Current.glueBlocks G Λ e₀ n_int n_ext e = n_int e := by
    intro e he
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hne : n_ext e = 0 := hne_off e (Finset.disjoint_left.mp hdisj he)
    have he0 : e ≠ e₀ := fun h => he0_int (h ▸ he)
    rw [if_neg he0]; omega
  have hg_ext : ∀ e ∈ Current.interiorEdges G Λ Cᶜ,
      Current.glueBlocks G Λ e₀ n_int n_ext e = n_ext e := by
    intro e he
    simp only [Current.glueBlocks, Current.add_apply,
      Current.fromEdgeFinset_singleton_apply]
    have hni : n_int e = 0 := hni_off e (Finset.disjoint_right.mp hdisj he)
    have he0 : e ≠ e₀ := fun h => he0_ext (h ▸ he)
    rw [if_neg he0]; omega
  have hint_prod : (∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ (Current.glueBlocks G Λ e₀ n_int n_ext e)
          / ((Current.glueBlocks G Λ e₀ n_int n_ext e).factorial : ℝ))
      = ∏ e ∈ Current.interiorEdges G Λ C,
          (β * J) ^ (n_int e) / ((n_int e).factorial : ℝ) :=
    Finset.prod_congr rfl (fun e he => by rw [hg_int e he])
  have hext_prod : (∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ (Current.glueBlocks G Λ e₀ n_int n_ext e)
          / ((Current.glueBlocks G Λ e₀ n_int n_ext e).factorial : ℝ))
      = ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
          (β * J) ^ (n_ext e) / ((n_ext e).factorial : ℝ) :=
    Finset.prod_congr rfl (fun e he => by rw [hg_ext e he])
  rw [Current.weight_pivotal_fiber_factor G Λ β J e₀
    (Current.glueBlocks G Λ e₀ n_int n_ext) x y a b C hab hpiv hC,
    hint_prod, hext_prod]
  ring

set_option linter.unusedDecidableInType false in
/-- **SL-D₁ weight-level `tsum` Fubini** (part 2b headline, spec `prop:fubini`,
eq. (sld1)). The pinned pivotal fiber weight sum factors as
\[
  \Sigma_C = \sum_{M \in 𝓕_C}' \weight(M)
    = (\beta J)\cdot \Xi_{\mathrm{int}}\cdot \Xi_{\mathrm{ext}}
    = (\beta J)\cdot
      \Bigl(\sum_{n \in 𝒜_{\mathrm{int}}}' w_{\mathrm{int}}(n)\Bigr)
      \cdot\Bigl(\sum_{n \in 𝒜_{\mathrm{ext}}}' w_{\mathrm{ext}}(n)\Bigr),
\]
with `Ξ_int`, `Ξ_ext` **ambient** block weight sums. Proof: reindex `Σ_C` along the
bijection `Φ` (`Equiv.tsum_eq`); the summand becomes `(βJ)·w_int·w_ext`
(`weight_glueBlocks_factor`); pull out `βJ` (`tsum_mul_left`) and split the product
`tsum` via `Summable.tsum_mul_tsum`, whose block-summability inputs are the part 2a
lemma `summable_block_weight_if_sourcesOn` (restricted by `Summable.subtype`). This
**completes SL-D₁ (range independence)**; it forms **no** subgraph current and does
**not** collapse `Ξ_ext` to a two-point function — that is the SL-D₂ core, which
**awaits explicit user authorisation and gates Lemma 5.1**. Part of ingredient
**SL-D₁** brick D1b part 2b (tracked ingredient, Group 1a); weight source FV (3.45). -/
theorem Current.pivotalNumerator_fiber_factor (β J : ℝ) (hβJ : 0 ≤ β * J)
    (e₀ : (inducedGraph G Λ).edgeSet) (C : Finset ↑Λ) (x y a b : ↑Λ)
    (hab : (e₀ : Sym2 ↑Λ) = s(a, b)) (haC : a ∈ C) (hbC : b ∉ C) :
    ∑' (M : ↥(Current.pivotalFiberSet G Λ e₀ C x y)),
        (M : Current G Λ).weight G Λ β J
      = (β * J)
        * (∑' (n : ↥(Current.interiorBlockSet G Λ C x a)),
            ∏ e ∈ Current.interiorEdges G Λ C,
              (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ))
        * ∑' (n : ↥(Current.exteriorBlockSet G Λ C b y)),
            ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
              (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
  classical
  have h_int : Summable (fun n : ↥(Current.interiorBlockSet G Λ C x a) =>
      ∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ)) := by
    have hs := (Current.summable_block_weight_if_sourcesOn G Λ hβJ
      (Current.interiorEdges G Λ C) (({x} : Finset ↑Λ) ∆ {a})).subtype
      (Current.interiorBlockSet G Λ C x a)
    refine hs.congr ?_
    rintro ⟨n, hn⟩
    exact if_pos ⟨hn.1, hn.2.1⟩
  have h_ext : Summable (fun n : ↥(Current.exteriorBlockSet G Λ C b y) =>
      ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ)) := by
    have hs := (Current.summable_block_weight_if_sourcesOn G Λ hβJ
      (Current.interiorEdges G Λ Cᶜ) (({b} : Finset ↑Λ) ∆ {y})).subtype
      (Current.exteriorBlockSet G Λ C b y)
    refine hs.congr ?_
    rintro ⟨n, hn⟩
    exact if_pos ⟨hn.1, hn.2⟩
  have hnn_int : (0 : ↥(Current.interiorBlockSet G Λ C x a) → ℝ) ≤
      fun n : ↥(Current.interiorBlockSet G Λ C x a) => ∏ e ∈ Current.interiorEdges G Λ C,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
    rw [Pi.le_def]
    intro n
    simp only [Pi.zero_apply]
    exact Finset.prod_nonneg
      (fun e _ => div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _))
  have hnn_ext : (0 : ↥(Current.exteriorBlockSet G Λ C b y) → ℝ) ≤
      fun n : ↥(Current.exteriorBlockSet G Λ C b y) => ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
        (β * J) ^ ((n : Current G Λ) e) / (((n : Current G Λ) e).factorial : ℝ) := by
    rw [Pi.le_def]
    intro n
    simp only [Pi.zero_apply]
    exact Finset.prod_nonneg
      (fun e _ => div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _))
  have hfg := h_int.mul_of_nonneg h_ext hnn_int hnn_ext
  rw [← Equiv.tsum_eq
    (Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm
    (fun M => (M : Current G Λ).weight G Λ β J)]
  have hpt : ∀ p : ↥(Current.interiorBlockSet G Λ C x a)
        × ↥(Current.exteriorBlockSet G Λ C b y),
      (((Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm p :
          ↥(Current.pivotalFiberSet G Λ e₀ C x y)) : Current G Λ).weight G Λ β J
        = (β * J) *
          ((∏ e ∈ Current.interiorEdges G Λ C,
              (β * J) ^ ((p.1 : Current G Λ) e)
                / (((p.1 : Current G Λ) e).factorial : ℝ))
            * ∏ e ∈ Current.interiorEdges G Λ Cᶜ,
              (β * J) ^ ((p.2 : Current G Λ) e)
                / (((p.2 : Current G Λ) e).factorial : ℝ)) := by
    intro p
    have hval := Current.weight_glueBlocks_factor G Λ β J e₀ C x y a b hab haC hbC
      (p.1 : Current G Λ) (p.2 : Current G Λ) p.1.2 p.2.2
    rw [show (((Current.pivotalFiberEquiv G Λ e₀ C x y a b hab haC hbC).symm p :
          ↥(Current.pivotalFiberSet G Λ e₀ C x y)) : Current G Λ)
        = Current.glueBlocks G Λ e₀ (p.1 : Current G Λ) (p.2 : Current G Λ) from rfl,
      hval]
    ring
  rw [tsum_congr hpt, tsum_mul_left, ← Summable.tsum_mul_tsum h_int h_ext hfg]
  ring

end Ambient

end IsingModel
