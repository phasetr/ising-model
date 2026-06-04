import IsingModel.Inequalities.SimonLiebIterateDecay
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d wrapper of the Simon-Lieb exponential-decay bound (FFS Ch 12 / GJ §18)

Specialises the abstract Simon-Lieb-iteration decay bound
`correlation_inducedGraph_le_pow_dist` to the physical cubic lattice
`latticeGraph d`, where every vertex of the induced subgraph has degree at most
`2d` (`inducedLatticeGraph_degree_le`).  The high-temperature parameter is
therefore `β J · 2d`, and the two-point function decays geometrically in the
induced-graph distance:

  `⟨σ_i σ_j⟩ ≤ (β J · 2d)^{dist(i, j) − 1}`,

tending to `0` with the distance in the high-temperature regime `β J · 2d < 1`.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d Simon-Lieb exponential decay** (FFS Ch 12 / GJ §18): on the cubic
lattice `latticeGraph d`, for reachable distinct sites `i, j` of the induced
subgraph on `Λ` (`0 < dist i j`),

`⟨σ_i σ_j⟩ ≤ (β J · 2d)^{dist(i, j) − 1}`,

which decays exponentially in the induced-graph distance in the high-temperature
regime `β J · 2d < 1`.  Specialises `correlation_inducedGraph_le_pow_dist` with the
induced-lattice degree bound `inducedLatticeGraph_degree_le` (`degree ≤ 2d`). -/
theorem correlation_inducedLatticeGraph_le_pow_dist (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ)) {i j : ↑Λ}
    (hdist : 0 < (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j) :
    correlation (inducedGraph (IsingModel.latticeGraph d) Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * (d : ℝ)))
          ^ ((inducedGraph (IsingModel.latticeGraph d) Λ).dist i j - 1) := by
  have hD : ∀ v : ↑Λ,
      ((inducedGraph (IsingModel.latticeGraph d) Λ).neighborFinset v).card ≤ 2 * d :=
    fun v => inducedLatticeGraph_degree_le d Λ v
  have h := correlation_inducedGraph_le_pow_dist (IsingModel.latticeGraph d) Λ hf hD hdist
  rwa [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring] at h

end Ambient

end IsingModel
