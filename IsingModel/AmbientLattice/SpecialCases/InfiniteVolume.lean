import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolumeTruncated4

/-!
# The empty ambient graph, and the sign of the infinite-volume truncated two-point function

Statements for an ambient graph `G : SimpleGraph V` over an arbitrary vertex type.

Over an arbitrary finite subset of `V`, the induced subgraph of the empty ambient graph is
again the empty graph. That statement is a `simp` lemma, carries no Prop-valued hypothesis,
and omits `DecidableEq V`.

Along an exhaustion `Λ` of `V`, the infinite-volume truncated two-point function of a
parameter triple `p : IsingParams ℝ` is nonnegative at every pair of sites `i j : V`, with
`Ferromagnetic p` as its only Prop-valued hypothesis. That statement takes `DecidableEq V`
and the stagewise `Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Induced subgraph of the empty graph is empty**:
`inducedGraph (⊥ : SimpleGraph V) Λ = ⊥`.

`inducedGraph = induce = comap` and `SimpleGraph.comap_bot`.
Useful rewrite when the ambient graph is `⊥` (free-spin limit). -/
@[simp]
theorem inducedGraph_bot (Λ : Finset V) :
    inducedGraph (⊥ : SimpleGraph V) Λ = (⊥ : SimpleGraph (↑Λ : Type _)) :=
  SimpleGraph.comap_bot _

/-- **η ≥ 0 at infinite volume** (GJ §17.7 Thm 17.7.1, infinite-volume
lattice version). Explicit alias of `truncated2Infinite_nonneg` matching the
`eta_nonneg_finite_vol` naming convention. -/
theorem eta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j :=
  truncated2Infinite_nonneg G Λ p hf i j

end Ambient
end IsingModel
