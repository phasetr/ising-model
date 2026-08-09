import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPair
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPairCorollaries

/-!
# ℤ^d along-exhaustion adjacency pair bounds and complete-summary bundles at zero field

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`: for sites of `Λ.volume n` adjacent in the
ambient lattice graph, the lower bound `tanh (β * J) / 2 ^ |E_n|` on the stage-`n` pair
correlation and, under a strict sign condition, its strict positivity — each stated for
`correlationΛ` on `Λ.volume n` rather than for `correlationAlongExhaustion`; and bundles
collecting, for the partition function and for the free-energy density, the high-temperature
lower and upper bounds together with the values taken at `⟨0, 0, β⟩` and at `⟨J, 0, 0⟩`. The
tanh lower bound and the bundles assume `0 ≤ β * J`, the strict positivity assumes
`0 < β * J`, and the free-energy bundle additionally needs `Λ.volume n` nonempty.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex pair single-edge tanh lower bound via lattice adjacency
at stage `n`**: under `0 ≤ β·J` and `(latticeGraph d).Adj ↑i ↑j` for
`i, j : ↑(Λ.volume n)`, the lifted pair correlation satisfies the
single-edge tanh lower bound. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n))
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    Real.tanh (β * J) /
        (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    d (Λ.volume n) J β hβJ i j hij

/-- **ℤ^d along-ex pair strict positivity via lattice adjacency at stage `n`**:
under `0 < β·J` and `(latticeGraph d).Adj ↑i ↑j`,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ) (i j : ↑(Λ.volume n))
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    d (Λ.volume n) J β hβJ i j hij

/-- **ℤ^d along-ex Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
at every stage `n` packages along-exhaustion Z lower bound, upper bound,
and trivial-slice values at `J = 0` / `β = 0`. ℤ^d wrapper of
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary`. -/
theorem
    partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ (2 : ℝ) ^ ((Λ.volume n).card +
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) *
            Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex freeEnergy complete-summary bundle at h = 0**: under
`0 ≤ β·J` and `(Λ.volume n).Nonempty`, at every stage `n` packages
along-exhaustion freeEnergy lower / upper bounds and trivial-slice
values at `J = 0` / `β = 0` (both = `log 2`). ℤ^d wrapper of
`freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary`. -/
theorem
    freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.log 2 +
            ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
              (Λ.volume n).card *
                Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

end Ambient

end IsingModel
