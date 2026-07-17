import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d partitionFunctionΛ disjoint_union ≤ wrappers

Narrow child module for two ℤ^d
`{log_,}partitionFunctionΛ_latticeGraph_le_of_disjoint_union`
wrappers extracted from `PartitionFreeEnergySuperadditivity.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `log Z_{Λ₁} ≤ log Z_{Λ₁ ∪ Λ₂}`** on disjoint unions (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p)
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p) := by
  classical
  exact log_partitionFunctionΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `Z_{Λ₁} ≤ Z_{Λ₁ ∪ Λ₂}`** on disjoint unions (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p := by
  classical
  exact partitionFunctionΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hd p hf

end Ambient
end IsingModel
