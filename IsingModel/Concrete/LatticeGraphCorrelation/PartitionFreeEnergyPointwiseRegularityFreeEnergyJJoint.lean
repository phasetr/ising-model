import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularityFE

/-!
# ℤ^d pointwise regularity of the free-energy density in the coupling and jointly

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the pointwise regularity of the free-energy density in
the coupling with the field and the inverse temperature fixed, and jointly in the triple
`(β, J, h)` read off a point of `ℝ × ℝ × ℝ`: `ContinuousAt` and `DifferentiableAt ℝ` in each
case. No sign condition on any parameter is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` ContinuousAt J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` DifferentiableAt J**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_J
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` jointly ContinuousAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.freeEnergyAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ n p

/-- **ℤ^d along-ex: `freeEnergyAlongExhaustion` jointly DifferentiableAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.freeEnergyAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ n p

end Ambient
end IsingModel
