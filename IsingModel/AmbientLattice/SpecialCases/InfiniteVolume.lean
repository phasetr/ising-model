import IsingModel.AmbientLattice.TruncatedFunctions

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

/-- **ζ ≥ 0 at infinite volume** (GJ §17.7 Thm 17.7.1, infinite-volume
lattice version, at `h = 0`). Explicit alias of
`truncated4Infinite_nonpos_h_zero`: `U₄^∞ ≤ 0` for pairwise-distinct sites at
`h = 0`. -/
theorem zeta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

/-- **Absence of even bound states, infinite-volume lattice form**
(Glimm-Jaffe §17.2, pp. 311-313). Infinite-volume version of
`IsingModel.absence_of_even_bound_states_finite_vol`: `U₄^∞(i,j,k,l) ≤ 0` for
ferromagnetic `⟨J, 0, β⟩` and pairwise-distinct sites. Explicit alias of
`truncated4Infinite_nonpos_h_zero`. -/
theorem absence_of_even_bound_states_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

end Ambient
end IsingModel
