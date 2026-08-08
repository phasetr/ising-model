import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT correlation pair wrappers

Instantiates the Λ-level zero-field two-site correlation estimates of GJ §18.3 at
`IsingModel.latticeGraph d`: strict positivity across an edge and the `tanh`-power lower
bound, in general and ferromagnetic form.
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

end Ambient

end IsingModel
