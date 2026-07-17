import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPair

/-!
# Concrete HT correlation pair corollaries (latticeAdj + trivial slices)

Narrow child module for 4 ℤ^d Λ-level correlation non-edge-based
corollaries extracted from `HighTemperatureBoundsCorrelationPair.lean`:

* `correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj`,
* `correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj`,
* `correlationΛ_latticeGraph_high_temp_h_zero_at_singleton`,
* `correlationΛ_latticeGraph_high_temp_h_zero_odd_card_eq_zero`.

The two `_of_latticeAdj` corollaries are `induce_adj`-bridged from
the corresponding edge-based wrappers in the parent. The singleton
and odd-card lemmas are direct thin pass-throughs of the ambient
`correlationΛ_high_temp_h_zero_at_singleton` and
`correlationΛ_high_temp_h_zero_odd_card_eq_zero` lemmas at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsCorrelationPair` declarations.
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
