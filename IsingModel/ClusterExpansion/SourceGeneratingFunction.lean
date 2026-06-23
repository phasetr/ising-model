import IsingModel.Conditioning.EdgeSetHandshake

/-!
# Source generating function for the two-point cluster expansion (GJ §18.4–18.7)

First brick of the **source-derivative cluster expansion** route to a volume-uniform bound on the
complex two-point correlation (Issue #4230, item D of #4214; the remaining Ising input `hbdd`).

The two-point correlation is the intensive ratio `Q_{i,j}(t) / Q_∅(t)` of subgraph-activity sums
(`correlationComplex_high_temp_expansion_h_zero_closed_on_ball`, with `t = tanh(βJ)`), where
`Q_A(t) = ∑_{X : ∂X = A} t^{|X|}` and `∂X` is the odd-degree vertex set of the edge subset `X`.  To
expose the **cancellation of the extensive part** of this ratio (the route that gives a
volume-uniform bound, per the cluster-expansion analysis — bounding the *ratio*, not numerator and
denominator separately), one introduces the **source generating function**
`SourceQ G t y = ∑_X t^{|X|} ∏_{v ∈ ∂X} y_v`.  Specializing the sources to `y_v = s · [v ∈ {i,j}]`
collapses, by the handshake lemma (`|∂X|` is even, so `∂X ⊆ {i,j}` forces `∂X ∈ {∅, {i,j}}`), to a
quadratic in `s`:
\[
  \texttt{SourceQ}\,G\,t\,(s \cdot \mathbf 1_{\{i,j\}})
    = Q_∅(t) + Q_{\{i,j\}}(t) \cdot s^2,
\]
so the two-point ratio `Q_{\{i,j\}}/Q_∅` is the `s^2`-coefficient ratio — the entry point for the
source-marked Mayer/cluster expansion (later bricks) and the volume-uniform anchored bound.

## Main results
* `oddBoundary` — the odd-degree vertex set `∂X` of an edge subset.
* `htSubgraphSum` — `Q_A(t) = ∑_{X : ∂X = A} t^{|X|}`.
* `sourceGenerating` — `SourceQ G t y = ∑_X t^{|X|} ∏_{v∈∂X} y_v`.
* `sourceGenerating_twoPoint_eq` — the quadratic collapse `= Q_∅ + Q_{\{i,j\}}·s^2`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Odd-degree vertex set (`∂X`)** of an edge subset `X`: the vertices incident to an odd number
of edges of `X`.  Its cardinality is always even (handshake, `even_card_odd_filter_card`). -/
def oddBoundary (X : Finset (Sym2 ι)) : Finset ι :=
  Finset.univ.filter (fun v => Odd ((X.filter (v ∈ ·)).card))

/-- The handshake parity of the odd-degree vertex set: `|∂X|` is even, for `X ⊆ G.edgeFinset`. -/
theorem oddBoundary_card_even (G : SimpleGraph ι) [Fintype G.edgeSet]
    {X : Finset (Sym2 ι)} (hX : X ∈ G.edgeFinset.powerset) :
    Even (oddBoundary X).card :=
  even_card_odd_filter_card G X (Finset.mem_powerset.mp hX)

/-- **Subgraph-activity sum** `Q_A(t) = ∑_{X : ∂X = A} t^{|X|}` (the high-temperature two-point
numerator/denominator; the denominator is the `A = ∅` instance). -/
noncomputable def htSubgraphSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (t : ℂ) : ℂ :=
  ∑ X ∈ G.edgeFinset.powerset.filter (fun X => oddBoundary X = A), t ^ X.card

/-- **Source generating function** `SourceQ G t y = ∑_X t^{|X|} ∏_{v ∈ ∂X} y_v` (sources `y` on
vertices). -/
noncomputable def sourceGenerating (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℂ) (y : ι → ℂ) : ℂ :=
  ∑ X ∈ G.edgeFinset.powerset, t ^ X.card * ∏ v ∈ oddBoundary X, y v

omit [Fintype ι] in
/-- A subset of a pair `{i, j}` with `i ≠ j` and even cardinality is `∅` or `{i, j}`. -/
private theorem subset_pair_of_even_card {i j : ι} (hij : i ≠ j)
    {B : Finset ι} (hsub : B ⊆ ({i, j} : Finset ι)) (heven : Even B.card) :
    B = ∅ ∨ B = ({i, j} : Finset ι) := by
  classical
  have hle : B.card ≤ 2 := le_trans (Finset.card_le_card hsub) (by simp [Finset.card_pair hij])
  have hc : B.card = 0 ∨ B.card = 2 := by rcases heven with ⟨m, hm⟩; omega
  rcases hc with h | h
  · exact Or.inl (Finset.card_eq_zero.mp h)
  · refine Or.inr (Finset.eq_of_subset_of_card_le hsub ?_)
    rw [Finset.card_pair hij]; omega

/-- The source product `∏_{v ∈ ∂X} (s · [v ∈ {i,j}])` is `1` if `∂X = ∅`, `s^2` if `∂X = {i,j}`, and
`0` otherwise (handshake: `∂X ⊆ {i,j}` with `|∂X|` even forces `∂X ∈ {∅, {i,j}}`). -/
theorem sourceGenerating_twoPoint_weight (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) {X : Finset (Sym2 ι)} (hX : X ∈ G.edgeFinset.powerset) (s : ℂ) :
    (∏ v ∈ oddBoundary X, if v ∈ ({i, j} : Finset ι) then s else 0)
      = if oddBoundary X = (∅ : Finset ι) then 1
        else if oddBoundary X = ({i, j} : Finset ι) then s ^ 2 else 0 := by
  classical
  have hPne : ({i, j} : Finset ι) ≠ (∅ : Finset ι) := by
    rw [← Finset.nonempty_iff_ne_empty]; exact ⟨i, by simp⟩
  by_cases hsub : oddBoundary X ⊆ ({i, j} : Finset ι)
  · rcases subset_pair_of_even_card hij hsub (oddBoundary_card_even G hX) with h0 | hpair
    · simp [h0]
    · rw [hpair, Finset.prod_pair hij]
      simp [hij, sq, hPne]
  · obtain ⟨v, hvB, hvA⟩ := Finset.not_subset.mp hsub
    have hprod : (∏ v ∈ oddBoundary X, if v ∈ ({i, j} : Finset ι) then s else 0) = 0 :=
      Finset.prod_eq_zero hvB (by simp [hvA])
    have hne0 : oddBoundary X ≠ (∅ : Finset ι) := fun h => hsub (by rw [h]; exact empty_subset _)
    have hneP : oddBoundary X ≠ ({i, j} : Finset ι) := fun h => hsub (by rw [h])
    rw [hprod]; simp [hne0, hneP]

/-- **Quadratic collapse of the source generating function at a two-point source** (GJ §18.4–18.7):
`SourceQ G t (s · 𝟙_{i,j}) = Q_∅(t) + Q_{i,j}(t)·s^2`.  The two-point ratio `Q_{i,j}/Q_∅` is thus
the `s^2`-coefficient ratio — the entry point for the source-marked cluster expansion. -/
theorem sourceGenerating_twoPoint_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j) (t s : ℂ) :
    sourceGenerating G t (fun v => if v ∈ ({i, j} : Finset ι) then s else 0)
      = htSubgraphSum G (∅ : Finset ι) t + htSubgraphSum G ({i, j} : Finset ι) t * s ^ 2 := by
  classical
  have hne : (∅ : Finset ι) ≠ ({i, j} : Finset ι) := by
    rw [ne_comm, ← Finset.nonempty_iff_ne_empty]; exact ⟨i, by simp⟩
  have hterm : ∀ X ∈ G.edgeFinset.powerset,
      t ^ X.card * ∏ v ∈ oddBoundary X, (if v ∈ ({i, j} : Finset ι) then s else 0)
        = (if oddBoundary X = (∅ : Finset ι) then t ^ X.card else 0)
          + (if oddBoundary X = ({i, j} : Finset ι) then t ^ X.card else 0) * s ^ 2 := by
    intro X hX
    rw [sourceGenerating_twoPoint_weight G hij hX s]
    by_cases h0 : oddBoundary X = (∅ : Finset ι)
    · simp [h0, hne]
    · by_cases hP : oddBoundary X = ({i, j} : Finset ι) <;> simp [h0, hP, Ne.symm hne]
  unfold sourceGenerating htSubgraphSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_filter]
  · rw [Finset.sum_filter, Finset.sum_mul]

end IsingModel
