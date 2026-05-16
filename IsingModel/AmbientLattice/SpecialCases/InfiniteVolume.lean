import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolumeTruncated4

/-!
# Infinite-volume special-case aliases

This module contains lightweight ambient special-case APIs that depend only on
the infinite-volume truncated-correlation layer. Keeping them outside the original
special-cases body lets concrete correlation modules use these aliases without
importing the analytic or cluster-expansion stack.
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

/-! ## Critical exponents at infinite volume (GJ §17.7 Thm 17.7.1) -/

/-- **η ≥ 0 at infinite volume** (GJ §17.7 Thm 17.7.1, infinite-volume
lattice version). Explicit alias of `truncated2Infinite_nonneg` matching the
`eta_nonneg_finite_vol` naming convention. -/
theorem eta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j :=
  truncated2Infinite_nonneg G Λ p hf i j

/-! ## Moved: 2 `truncated4Infinite` ζ/U₄ aliases at `h = 0`

The two `truncated4Infinite_nonpos_h_zero` aliases
(`zeta_nonneg_infinite_vol`,
`absence_of_even_bound_states_infinite_vol`) now live in
`IsingModel.AmbientLattice.SpecialCases.InfiniteVolumeTruncated4`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
