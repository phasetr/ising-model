import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDecayLatticeGraph

/-!
# ℓ¹ lattice-distance form of the Simon-Lieb exponential decay (FFS Ch 12 / GJ §18)

The induced-graph-distance decay `correlation_inducedLatticeGraph_le_pow_dist`
refines to a bound in the physical **ℓ¹ lattice distance**.  A walk in the induced
subgraph maps (via the inclusion `↑Λ ↪ ℤ^d`) to a walk in `latticeGraph d` of the
same length, so `latticeDistance ↑i ↑j ≤ dist i j`
(`latticeDistance_le_inducedGraph_dist`); in the high-temperature regime
`β J · 2d ≤ 1` the base `β J · 2d ≤ 1` makes the geometric bound monotone, giving

  `⟨σ_i σ_j⟩ ≤ (β J · 2d)^{latticeDistance(i, j) − 1}`,

exponential decay in the ℓ¹ lattice distance.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality*
  (1992), Ch 12.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel

namespace Ambient

/-- **ℓ¹ lattice distance bounds the induced-graph distance**: for reachable
sites `i, j` of the induced subgraph on `Λ`, the ℓ¹ lattice distance of their
images is at most their induced-graph distance.  A minimal induced-graph walk maps
to a `latticeGraph d` walk of the same length (`SimpleGraph.Embedding.induce`),
and the ambient lattice-graph distance equals the ℓ¹ distance
(`latticeGraph_dist_eq_latticeDistance`). -/
theorem latticeDistance_le_inducedGraph_dist (d : ℕ) (Λ : Finset (Fin d → ℤ)) {i j : ↑Λ}
    (hr : (inducedGraph (IsingModel.latticeGraph d) Λ).Reachable i j) :
    latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ)
      ≤ (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← latticeGraph_dist_eq_latticeDistance]
  calc (IsingModel.latticeGraph d).dist (i : Fin d → ℤ) (j : Fin d → ℤ)
      ≤ (p.map (SimpleGraph.Embedding.induce (↑Λ : Set (Fin d → ℤ))).toHom).length :=
        SimpleGraph.dist_le _
    _ = p.length := SimpleGraph.Walk.length_map _ _
    _ = (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j := hp

/-- **ℓ¹ lattice-distance Simon-Lieb exponential decay** (FFS Ch 12 / GJ §18): on
the cubic lattice, in the high-temperature regime `β J · 2d ≤ 1`, for reachable
distinct sites `i, j` (`0 < dist i j`),

`⟨σ_i σ_j⟩ ≤ (β J · 2d)^{latticeDistance(i, j) − 1}`,

exponential decay in the ℓ¹ lattice distance.  Refines
`correlation_inducedLatticeGraph_le_pow_dist` using `latticeDistance ≤ dist` and
the monotonicity of `a^·` for `0 ≤ a ≤ 1`. -/
theorem correlation_inducedLatticeGraph_le_pow_latticeDistance (d : ℕ)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hβJ2d : β * J * (2 * (d : ℝ)) ≤ 1) {i j : ↑Λ}
    (hdist : 0 < (inducedGraph (IsingModel.latticeGraph d) Λ).dist i j) :
    correlation (inducedGraph (IsingModel.latticeGraph d) Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * (2 * (d : ℝ)))
          ^ (latticeDistance d (i : Fin d → ℤ) (j : Fin d → ℤ) - 1) := by
  have hr : (inducedGraph (IsingModel.latticeGraph d) Λ).Reachable i j := by
    by_contra hnr
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hnr)] at hdist
    exact absurd hdist (lt_irrefl 0)
  have hle := latticeDistance_le_inducedGraph_dist d Λ hr
  have hbase := correlation_inducedLatticeGraph_le_pow_dist d Λ hf hdist
  have hnonneg : 0 ≤ β * J * (2 * (d : ℝ)) :=
    mul_nonneg (mul_nonneg hf.hβ.le hf.hJ) (by positivity)
  refine le_trans hbase ?_
  exact pow_le_pow_of_le_one hnonneg hβJ2d (by omega)

end Ambient

end IsingModel
