import IsingModel.Inequalities.WalkSumTsum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d wrapper of the infinite walk-sum representation (FFS Ch 12 / GJ §18)

Specialises the abstract random-walk upper representation
`correlation_inducedGraph_le_tsum_walkSum` to the physical cubic lattice
`latticeGraph d`, where every induced-subgraph vertex has degree at most `2d`
(`inducedLatticeGraph_degree_le`).  In the high-temperature regime `β J · 2d < 1`,

  `⟨σ_i σ_j⟩ ≤ ∑_{k≥1} walkSum (β J) i j k`,

the ℤ^d concrete form of the discrete random-walk bound on the Ising two-point
function.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d infinite walk-sum representation** (FFS Ch 12 / GJ §18): on the cubic
lattice `latticeGraph d`, in the high-temperature regime `β J · 2d < 1`, for
distinct sites `i ≠ j` of the induced subgraph on `Λ`,

`⟨σ_i σ_j⟩ ≤ ∑_{k≥1} walkSum (β J) i j k`,

the discrete random-walk upper bound on the Ising two-point function.  Specialises
`correlation_inducedGraph_le_tsum_walkSum` with the induced-lattice degree bound
`inducedLatticeGraph_degree_le` (`degree ≤ 2d`). -/
theorem correlation_inducedLatticeGraph_le_tsum_walkSum (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hlt : β * J * (2 * (d : ℝ)) < 1) {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph (IsingModel.latticeGraph d) Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ ∑' k : ℕ, walkSum (inducedGraph (IsingModel.latticeGraph d) Λ) (β * J) i j (k + 1) := by
  have hD : ∀ v : ↑Λ,
      ((inducedGraph (IsingModel.latticeGraph d) Λ).neighborFinset v).card ≤ 2 * d :=
    fun v => inducedLatticeGraph_degree_le d Λ v
  have hlt' : β * J * ((2 * d : ℕ) : ℝ) < 1 := by
    rwa [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring]
  exact correlation_inducedGraph_le_tsum_walkSum (IsingModel.latticeGraph d) Λ hf hD hlt' hij

end Ambient

end IsingModel
