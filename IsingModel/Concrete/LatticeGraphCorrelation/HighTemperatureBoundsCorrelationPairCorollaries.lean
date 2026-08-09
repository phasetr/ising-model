import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPair

/-!
# ℤ^d fixed-volume pair bounds from ambient adjacency, and odd-observable vanishing

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ` and at the parameter
record `⟨J, 0, β⟩`, the pair-correlation lower bound `tanh (β * J) / 2 ^ |E_Λ|` and the strict
positivity of the pair correlation for sites adjacent in the ambient lattice graph, obtained
by rewriting that adjacency into membership of the induced edge set through
`SimpleGraph.induce_adj`; together with the vanishing of the single-site correlation and the
vanishing of the correlation at any observable of odd cardinality. The lower bound assumes
`0 ≤ β * J` and the strict positivity assumes `0 < β * J`, each of them together with the
ambient adjacency; the single-site vanishing carries no hypothesis, and the odd-observable
vanishing carries only the parity of the observable's cardinality.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ pair single-edge tanh lower bound via lattice adjacency**:
under `0 ≤ β·J` and `(latticeGraph d).Adj ↑i ↑j` (i.e.
`latticeDistance d ↑i ↑j = 1`),
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. Direct corollary of
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`,
removing the explicit edge-set membership in favour of the more
familiar lattice adjacency on the ambient lattice. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ)
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) := by
  have hne : i ≠ j := by
    intro h
    apply hij.ne
    exact congrArg Subtype.val h
  have he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).mpr hij
  exact correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    d Λ J β hβJ i j hne he

/-- **ℤ^d Λ pair strict positivity via lattice adjacency**: under
`0 < β·J` and `(latticeGraph d).Adj ↑i ↑j`,
`0 < ⟨σ_iσ_j⟩^Λ`. Direct corollary of
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (i j : ↑Λ)
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) := by
  have hne : i ≠ j := by
    intro h
    apply hij.ne
    exact congrArg Subtype.val h
  have he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).mpr hij
  exact correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    d Λ J β hβJ i j hne he

/-- **ℤ^d Λ-level magnetization vanishes at h = 0**:
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i} = 0` for any `i : ↑Λ`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_at_singleton`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ-level Z₂ symmetry of correlation at h = 0 via handshake**:
for `A : Finset ↑Λ` of odd cardinality,
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ A = 0`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_odd_card_eq_zero`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_odd_card_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_high_temp_h_zero_odd_card_eq_zero
    (IsingModel.latticeGraph d) Λ J β A hA_odd

end Ambient

end IsingModel
