import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchEndpoint
import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.PosReal.ViaLocal

/-!
# ℤ^d unconditional positive-real holomorphic extension (GJ §4.6 Thm 4.6.2)

Thin ℤ^d pass-through of the unconditional global-branch endpoint: the subsequential
compact-target patch toward GJ Theorem 4.6.2 on `latticeGraph d` with any exhaustion
satisfying bounded edge density and the disjoint-tower hypotheses.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d unconditional subsequential compact-target patch toward GJ Theorem 4.6.2**: for
positive real ferromagnetic parameters on `latticeGraph d`, bounded edge density,
disjoint-tower hypotheses, and a compact Lee-Yang target containing the physical field, there
are an open neighbourhood of the target, a stage subsequence, and a function holomorphic
there which is the pointwise limit of the subsequenced global branch logarithms, with value
the infinite-volume free energy at the physical field. -/
theorem
    freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_latticeGraph
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
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ IsingModel.leeYangDomain ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g U ∧
          (∀ z ∈ U, Filter.Tendsto
            (fun m => Ambient.globalBranchStage (IsingModel.latticeGraph d) Λ
              (p.J : ℂ) (p.β : ℂ) (p.h : ℂ) (σ m) z)
            Filter.atTop (nhds (g z))) ∧
          g (p.h : ℂ) =
            ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

end Ambient
end IsingModel
