import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.SpinSums

/-!
# The current carried by a Finset of edges

`Current.fromEdgeFinset G Λ S` is the current that assigns multiplicity `1` to every edge in
`S` and `0` to every other edge of `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces,
for an arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`.

Its weight and support are computed for an arbitrary `S`, and its parity and source set for a
one-edge `S`. At the empty edge `Finset` it is the zero current. Its support — the edges at
which it is nonzero — is `S` itself. Its weight is `(β * J)` raised to the number of edges of
`S`, for arbitrary real `β` and `J`.

At a one-edge `Finset {e₀}` the parity at a vertex `v` is `1` in `ZMod 2` when `v` lies on
`e₀` and `0` otherwise, so the source set is the endpoint `Finset` of `e₀`; and that source
set has cardinality `2`, because an edge of a simple graph is not a diagonal pair.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]` together with
`[DecidableEq ↥Λ]`, and none carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Edge-subset current**: the current that takes value `1` on
edges in `S` and `0` elsewhere. The basic 0/1 currents that
form the underlying combinatorial substrate of the random-current
sum (each finite-support current is a sum of indicator currents
weighted by edge multiplicities). -/
def Current.fromEdgeFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) : Current G Λ :=
  fun e => if e ∈ S then 1 else 0

omit [DecidableEq V] in
/-- **`fromEdgeFinset` of empty set is the zero current**. -/
@[simp]
theorem Current.fromEdgeFinset_empty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.fromEdgeFinset G Λ (∅ : Finset (inducedGraph G Λ).edgeSet)
      = (0 : Current G Λ) := by
  funext e
  simp [Current.fromEdgeFinset]

omit [DecidableEq V] in
/-- **Weight of `fromEdgeFinset S`**: equals `(β J)^(S.card)`
since each edge in `S` contributes `(β J)^1 / 1! = β J` and each
edge outside `S` contributes `(β J)^0 / 0! = 1`. -/
theorem Current.fromEdgeFinset_weight (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (β J : ℝ) :
    (Current.fromEdgeFinset G Λ S).weight G Λ β J = (β * J)^(S.card) := by
  unfold Current.weight Current.fromEdgeFinset
  -- factorials are all 1 (since (if … then 1 else 0).factorial = 1)
  have h_factorial : ∀ e : (inducedGraph G Λ).edgeSet,
      ((if e ∈ S then 1 else 0 : ℕ).factorial : ℝ) = 1 := by
    intro e; by_cases he : e ∈ S <;> simp [he]
  simp_rw [h_factorial, div_one]
  -- Reduce (β * J)^(if e ∈ S then 1 else 0) to ite (β * J) 1.
  have h_pow : ∀ e : (inducedGraph G Λ).edgeSet,
      (β * J)^(if e ∈ S then 1 else 0 : ℕ) = if e ∈ S then β * J else 1 := by
    intro e; by_cases he : e ∈ S <;> simp [he]
  simp_rw [h_pow]
  -- ∏ e ∈ univ, (if e ∈ S then β J else 1) = (β J)^|S|
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_univ_mem]

omit [DecidableEq V] in
/-- **Support of `fromEdgeFinset S` is `S`**: the set of edges
where the 0/1 indicator current is non-zero is exactly `S`. -/
@[simp]
theorem Current.fromEdgeFinset_support (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) :
    (Current.fromEdgeFinset G Λ S).support G Λ = S := by
  classical
  ext e
  simp only [Current.support, Current.fromEdgeFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases he : e ∈ S
  · simp [he]
  · simp [he]

omit [DecidableEq V] in
/-- **Parity of `fromEdgeFinset {e₀}` at vertex `v`**: equals `1`
in `ZMod 2` iff `v` is an endpoint of `e₀`, else `0`. -/
theorem Current.fromEdgeFinset_singleton_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ {e₀}).parity G Λ v
      = if v ∈ (e₀ : Sym2 ↑Λ) then (1 : ZMod 2) else 0 := by
  unfold Current.parity Current.fromEdgeFinset
  -- ∑ e, if v ∈ e then ((if e ∈ {e₀} then 1 else 0 : ℕ) : ZMod 2) else 0
  rw [Finset.sum_eq_single e₀]
  · -- main term: e = e₀ contributes (if v ∈ e₀ then 1 else 0)
    by_cases hv : v ∈ (e₀ : Sym2 ↑Λ)
    · simp [hv, Finset.mem_singleton]
    · simp [hv]
  · -- other terms: e ≠ e₀ contribute 0 since e ∉ {e₀}
    intro b _ hb_ne
    have : b ∉ ({e₀} : Finset _) := Finset.notMem_singleton.mpr hb_ne
    by_cases hv : v ∈ (b : Sym2 ↑Λ)
    · simp [hv, this]
    · simp [hv]
  · -- e₀ ∈ univ
    intro h
    exact absurd (Finset.mem_univ e₀) h

omit [DecidableEq V] in
/-- **Sources of `fromEdgeFinset {e₀}`**: equals the endpoint
finset of `e₀`, i.e. `(e₀ : Sym2 ↑Λ).toFinset`. Direct
consequence of `fromEdgeFinset_singleton_parity` and
`mem_sources_iff`. -/
@[simp]
theorem Current.fromEdgeFinset_singleton_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) :
    (Current.fromEdgeFinset G Λ {e₀}).sources G Λ
      = (e₀ : Sym2 ↑Λ).toFinset := by
  classical
  ext v
  rw [Current.mem_sources_iff, Current.fromEdgeFinset_singleton_parity,
      Sym2.mem_toFinset]
  by_cases hv : v ∈ (e₀ : Sym2 ↑Λ) <;> simp [hv]

omit [DecidableEq V] in
/-- **Cardinality of `fromEdgeFinset {e₀}.sources` is `2`**: a
singleton-edge indicator current has exactly two sources, the two
endpoints of `e₀` in `↑Λ`. Distinctness comes from
`SimpleGraph.not_isDiag_of_mem_edgeSet` (the underlying
`inducedGraph` is loopless). -/
@[simp]
theorem Current.fromEdgeFinset_singleton_sources_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) :
    ((Current.fromEdgeFinset G Λ {e₀}).sources G Λ).card = 2 := by
  rw [Current.fromEdgeFinset_singleton_sources,
    Sym2.card_toFinset_of_not_isDiag _
      ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e₀.2)]


end Ambient
end IsingModel
