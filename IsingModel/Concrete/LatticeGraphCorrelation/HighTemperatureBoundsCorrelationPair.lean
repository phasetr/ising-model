import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansion
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationBasic

/-!
# Concrete HT correlation pair / singleton wrappers

Narrow child module for the 8 ℤ^d Λ-level correlation pair/singleton
wrappers (`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge`,
`_ferromagnetic`,
`_at_pair_ge_tanh_div_two_pow_edges`,
`_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`,
`_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj`,
`_at_pair_pos_of_latticeAdj`, `_at_singleton`, `_odd_card_eq_zero`)
extracted from `HighTemperatureBounds.lean` in PR #2070. Each is a
thin pass-through (or `induce_adj`-bridged corollary) to the
corresponding ambient `correlationΛ_high_temp_h_zero_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ pair correlation strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge in `inducedGraph (latticeGraph d) Λ`,
`0 < ⟨σ_iσ_j⟩^Λ`. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    (IsingModel.latticeGraph d) Λ J β hβJ i j hij he

/-- **ℤ^d Λ pair correlation single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ β·J` and an edge `s(i, j) ∈ (inducedGraph (latticeGraph d) Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (IsingModel.latticeGraph d) Λ J β hβJ i j hij he

/-- **ℤ^d Λ ferromagnetic pair single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ J, 0 < β` and an edge in `inducedGraph (latticeGraph d) Λ`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. ℤ^d wrapper. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j hij he

/-- **ℤ^d Λ ferromagnetic pair strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < J, 0 < β` and an edge in `inducedGraph (latticeGraph d) Λ`,
`0 < ⟨σ_iσ_j⟩^Λ`. ℤ^d wrapper. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j hij he

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
