import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchEndpoint
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.PosReal.ViaLocal

/-!
# ℤ^d unconditional positive-real holomorphic extension (GJ §4.6 Thm 4.6.2)

Thin ℤ^d pass-through of the unconditional global-branch endpoint: GJ Theorem 4.6.2 in
compact-target form on `latticeGraph d` with any exhaustion satisfying bounded edge density
and the disjoint-tower hypotheses.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d GJ Theorem 4.6.2, compact-target form (unconditional)**: for positive real
ferromagnetic parameters on `latticeGraph d`, bounded edge density, disjoint-tower
hypotheses, and a compact Lee-Yang target containing the physical field, there is a function
holomorphic on the target whose value at the physical field is the infinite-volume free
energy. -/
theorem
    freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β) (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

end Ambient
end IsingModel
