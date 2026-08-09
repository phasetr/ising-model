import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity

/-!
# ℤ^d pointwise regularity of the partition function in the field and jointly

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the pointwise regularity of the partition function in
the external field with the coupling and the inverse temperature fixed, and jointly in the
triple `(β, J, h)` read off a point of `ℝ × ℝ × ℝ`: `ContinuousAt` and `DifferentiableAt ℝ` in
each case. No sign condition on any parameter is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` ContinuousAt h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    ContinuousAt (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` DifferentiableAt h**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (fun h' : ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` jointly ContinuousAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.partitionFunctionAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ n p

/-- **ℤ^d along-ex: `partitionFunctionAlongExhaustion` jointly DifferentiableAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨q.2.1, q.2.2, q.1⟩ n) p :=
  Ambient.partitionFunctionAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ n p

end Ambient
end IsingModel
