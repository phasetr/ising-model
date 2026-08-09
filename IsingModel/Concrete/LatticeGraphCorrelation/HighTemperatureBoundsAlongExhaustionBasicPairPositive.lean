import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstonesEdge

/-!
# ℤ^d along-exhaustion pair correlations are strictly positive across an edge

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the strict positivity of the pair
correlation at distinct sites of `Λ.volume n` whose unordered pair lies in the edge set of the
stage-`n` induced subgraph. The statement is given under `0 < β * J` and again under the
ferromagnetic pair `0 < J` and `0 < β`; the distinctness and edge hypotheses are carried in
either form, and the conclusion is stated for `correlationΛ` on `Λ.volume n` rather than for
`correlationAlongExhaustion`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex pair correlation strict positivity under edge at stage `n`**:
under `0 < β·J` and an edge in the stage-`n` induced ℤ^d subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge
    (IsingModel.latticeGraph d) Λ J β hβJ n i j hij he

/-- **ℤ^d along-ex ferromagnetic pair strict positivity under edge at stage `n`**:
under `0 < J, 0 < β` and an edge in the stage-`n` induced ℤ^d subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. ℤ^d wrapper. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n i j hij he

end Ambient
end IsingModel
