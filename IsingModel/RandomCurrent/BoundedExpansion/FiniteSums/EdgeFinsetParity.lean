import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.EdgeFinsetBasic

/-!
# Parity, sources and incident degree of the current carried by an edge Finset

How the parity, the source set and the total incident degree of
`Current.fromEdgeFinset G Λ S` are read off from the edge `Finset` `S` alone, for an
arbitrary `G : SimpleGraph V`, an arbitrary finite volume `Λ : Finset V` and an arbitrary `S`
of edges of `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces.

At a vertex `v` the parity is the `ZMod 2` sum, over the edges `e ∈ S`, of `1` for those
containing `v` and `0` for the rest. Equivalently `v` belongs to the source set exactly when
the number of edges of `S` containing `v` is odd. Dropping the reduction modulo `2` gives the
natural-number counterpart: `Current.degreeAt G Λ (Current.fromEdgeFinset G Λ S) v`, the sum
of the multiplicities over the edges containing `v`, is that same number of edges.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]` together with
`[DecidableEq ↥Λ]`, and none carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **General `fromEdgeFinset` parity formula**: parity at vertex
`v` of the indicator current `fromEdgeFinset G Λ S` equals the
sum over edges `e ∈ S` incident to `v`, in `ZMod 2`. Generalises
the singleton-edge form `fromEdgeFinset_singleton_parity`. -/
theorem Current.fromEdgeFinset_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ S).parity G Λ v
      = ∑ e ∈ S, if v ∈ (e : Sym2 ↑Λ) then (1 : ZMod 2) else 0 := by
  unfold Current.parity Current.fromEdgeFinset
  -- swap inner ifs to get (∑ e ∈ univ, if e ∈ S then (if v ∈ e then 1 else 0) else 0)
  have hswap : ∀ e : (inducedGraph G Λ).edgeSet,
      (if v ∈ (e : Sym2 ↑Λ)
          then (((if e ∈ S then (1 : ℕ) else 0) : ℕ) : ZMod 2) else 0)
        = if e ∈ S
            then (if v ∈ (e : Sym2 ↑Λ) then (1 : ZMod 2) else 0) else 0 := by
    intro e
    by_cases he : e ∈ S
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
  simp_rw [hswap]
  -- ∑ e ∈ univ, if e ∈ S then f e else 0 = ∑ e ∈ S, f e
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp

omit [DecidableEq V] in
/-- **Source characterisation for `fromEdgeFinset`**: a vertex `v`
is a source of `fromEdgeFinset G Λ S` iff an odd number of edges
in `S` are incident to `v`. The standard combinatorial source
characterisation (FV §3.10.6), feeding the source-set
manipulations in the random-current expansion of `⟨σ_A⟩^Λ` and
the Aizenman switching lemma. -/
@[simp]
theorem Current.mem_fromEdgeFinset_sources_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    v ∈ (Current.fromEdgeFinset G Λ S).sources G Λ
      ↔ Odd (S.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card := by
  classical
  rw [Current.mem_sources_iff, Current.fromEdgeFinset_parity,
    Finset.sum_boole, Ne, ZMod.natCast_eq_zero_iff,
    ← even_iff_two_dvd, ← Nat.not_even_iff_odd]

omit [DecidableEq V] in
/-- **`degreeAt` of `fromEdgeFinset`**: equals the cardinality of
the edges in `S` incident to `v`. The ℕ-valued analogue of
`mem_fromEdgeFinset_sources_iff` (without the parity reduction). -/
@[simp]
theorem Current.fromEdgeFinset_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ S).degreeAt G Λ v
      = (S.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card := by
  classical
  unfold Current.degreeAt Current.fromEdgeFinset
  -- ∑ e : univ, if v ∈ e then (if e ∈ S then 1 else 0) else 0
  have hswap : ∀ e : (inducedGraph G Λ).edgeSet,
      (if v ∈ (e : Sym2 ↑Λ) then (if e ∈ S then (1 : ℕ) else 0) else 0)
        = if e ∈ S then (if v ∈ (e : Sym2 ↑Λ) then (1 : ℕ) else 0) else 0 := by
    intro e
    by_cases he : e ∈ S
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
  simp_rw [hswap]
  rw [← Finset.sum_filter]
  have huniv : (Finset.univ.filter
      (fun e : (inducedGraph G Λ).edgeSet => e ∈ S)) = S := by
    ext e; simp
  rw [huniv, Finset.sum_boole, Nat.cast_id]


end Ambient
end IsingModel
