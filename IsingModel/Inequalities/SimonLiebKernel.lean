import IsingModel.Inequalities.SimonLieb
import IsingModel.Inequalities.GKS

/-!
# Neighbour-vertex Simon-Lieb transfer kernel (GJ §18 / FFS Ch 12)

The Simon-Lieb edge-peeling inequality (`correlation_inducedGraph_simon_lieb`)
bounds a two-point correlation by a sum over the edges incident to one endpoint.
For the **random-walk representation** of the two-point function we recast this
as a one-step transfer over **neighbour vertices**: define the kernel

  `K(j, u) = if u = j then 1 else ⟨σ_u σ_j⟩`

(the `u = j` value collects the `{i,j} △ {i,j} = ∅` contribution, `⟨σ_∅⟩ = 1`),
so the Simon-Lieb inequality becomes

  `⟨σ_i σ_j⟩ ≤ β J · ∑_{u ∼ i} K(j, u)`.

Iterating this neighbour-vertex form (in later PRs) yields the random-walk bound
`⟨σ_i σ_j⟩ ≤ ∑_{walks i → j} (β J)^{length}`.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

open Finset

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Simon-Lieb neighbour-vertex transfer kernel**: `K(j, u) = ⟨σ_u σ_j⟩` for
`u ≠ j`, and `K(j, j) = 1` (the `∅`-correlation value that the diagonal edge
contributes). -/
noncomputable def simonLiebKernel (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (p : IsingParams ℝ) (j u : ↑Λ) : ℝ :=
  if u = j then 1 else correlation (inducedGraph G Λ) p {u, j}

omit [DecidableEq V] in
/-- The kernel on the diagonal is `1`. -/
@[simp]
theorem simonLiebKernel_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (p : IsingParams ℝ) (j : ↑Λ) :
    simonLiebKernel G Λ p j j = 1 := if_pos rfl

omit [DecidableEq V] in
/-- Off the diagonal the kernel is the two-point correlation. -/
theorem simonLiebKernel_of_ne (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (p : IsingParams ℝ) {j u : ↑Λ} (h : u ≠ j) :
    simonLiebKernel G Λ p j u = correlation (inducedGraph G Λ) p {u, j} := if_neg h

omit [DecidableEq V] in
/-- The kernel is nonnegative (GKS-I). -/
theorem simonLiebKernel_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {p : IsingParams ℝ} (hf : Ferromagnetic p) (j u : ↑Λ) :
    0 ≤ simonLiebKernel G Λ p j u := by
  rw [simonLiebKernel]
  split
  · exact zero_le_one
  · exact gks_first (inducedGraph G Λ) p hf {u, j}

omit [DecidableEq V] in
/-- The kernel is at most `1`. -/
theorem simonLiebKernel_le_one (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (p : IsingParams ℝ) (j u : ↑Λ) :
    simonLiebKernel G Λ p j u ≤ 1 := by
  rw [simonLiebKernel]
  split
  · exact le_refl 1
  · exact (abs_le.mp (abs_correlation_le_one (inducedGraph G Λ) p {u, j})).2

omit [DecidableEq V] in
/-- **Per-edge identification with the kernel**: for distinct `i ≠ j` and an edge
`e` incident to `i` with other endpoint `u = other e`,
`⟨σ^{{i,j} △ toFinset e}⟩ = K(j, u)`.  The `u = j` case is the `∅`-correlation
`1`; the `u ≠ j` case is `{i,j} △ {i,u} = {u,j}`. -/
theorem correlation_symmDiff_eq_simonLiebKernel (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (p : IsingParams ℝ) {i j : ↑Λ} (hij : i ≠ j)
    (e : (inducedGraph G Λ).edgeSet) (hi : i ∈ (e : Sym2 ↑Λ)) :
    correlation (inducedGraph G Λ) p (symmDiff {i, j} (e : Sym2 ↑Λ).toFinset)
      = simonLiebKernel G Λ p j (Sym2.Mem.other hi) := by
  set u := Sym2.Mem.other hi with hu
  have hiu : i ≠ u := (Sym2.other_ne (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2) hi).symm
  have he_tf : (e : Sym2 ↑Λ).toFinset = {i, u} := by
    have h := @Sym2.toFinset_mk_eq _ _ i u
    rwa [Sym2.other_spec hi] at h
  rw [he_tf]
  by_cases huj : u = j
  · rw [huj, symmDiff_self, Finset.bot_eq_empty, correlation_empty, simonLiebKernel, if_pos rfl]
  · rw [symmDiff_pair_pair_of_ne hij hiu huj, simonLiebKernel, if_neg huj]

set_option linter.unusedDecidableInType false in
/-- **Neighbour-vertex Simon-Lieb inequality** (GJ §18 / FFS Ch 12): for `h = 0`,
ferromagnetic `⟨J,0,β⟩`, and distinct `i ≠ j ∈ Λ`,

`⟨σ_i σ_j⟩ ≤ β J · ∑_{u ∈ neighborFinset i} K(j, u)`.

The one-step transfer-kernel form of the Simon-Lieb inequality: the edge sum of
`correlation_inducedGraph_simon_lieb` is reindexed to a sum over the neighbours
`u ∼ i` (the other endpoints of the incident edges) via `Finset.sum_bij'`. -/
theorem correlation_inducedGraph_simon_lieb_neighbor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J * ∑ u ∈ (inducedGraph G Λ).neighborFinset i,
          simonLiebKernel G Λ (⟨J, 0, β⟩ : IsingParams ℝ) j u := by
  have hβJ : 0 ≤ β * J := mul_nonneg hf.hβ.le hf.hJ
  refine le_trans (correlation_inducedGraph_simon_lieb G Λ hβJ hij) ?_
  apply mul_le_mul_of_nonneg_left _ hβJ
  apply le_of_eq
  refine Finset.sum_bij'
    (fun e he => Sym2.Mem.other ((Finset.mem_filter.mp he).2))
    (fun u hu => (⟨s(i, u), by
      rw [SimpleGraph.mem_edgeSet]; rwa [SimpleGraph.mem_neighborFinset] at hu⟩
        : (inducedGraph G Λ).edgeSet))
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into neighborFinset
    intro e he
    have h2 : i ∈ (e : Sym2 ↑Λ) := (Finset.mem_filter.mp he).2
    rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet, Sym2.other_spec h2]
    exact e.2
  · -- backward maps into edge filter
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Sym2.mem_mk_left i u⟩
  · -- left inverse
    intro e he
    apply Subtype.ext
    exact Sym2.other_spec ((Finset.mem_filter.mp he).2)
  · -- right inverse
    intro u hu
    have hadj : (inducedGraph G Λ).Adj i u := by rwa [SimpleGraph.mem_neighborFinset] at hu
    have hspec : s(i, Sym2.Mem.other (Sym2.mem_mk_left i u)) = s(i, u) :=
      Sym2.other_spec (Sym2.mem_mk_left i u)
    rw [Sym2.eq_iff] at hspec
    rcases hspec with ⟨_, h⟩ | ⟨hiu, _⟩
    · exact h
    · exact absurd hiu hadj.ne
  · -- values agree via the per-edge kernel identity
    intro e he
    exact correlation_symmDiff_eq_simonLiebKernel G Λ _ hij e ((Finset.mem_filter.mp he).2)

end Ambient

end IsingModel
