import IsingModel.AmbientLatticeSum.LambdaSuperadditivity
import IsingModel.Lattice

/-!
# ℤ^d super-multiplicativity of the partition function on disjoint unions

Instantiates at `IsingModel.latticeGraph d` the behaviour of the partition function under the
union of disjoint finite volumes: it is super-multiplicative and its logarithm is
super-additive, each under disjointness of the volumes and the ferromagnetic hypothesis on the
parameter record. A congruence statement transporting the partition function along an equality
of volumes is included; it assumes only that equality.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Z` is super-multiplicative on disjoint Finset unions**
(ferromagnetic). Direct wrapper of `partitionFunctionΛ_disjUnion_super_multiplicative`. -/
theorem partitionFunctionΛ_latticeGraph_disjUnion_super_multiplicative
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      * partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p :=
  partitionFunctionΛ_disjUnion_super_multiplicative
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `log Z` is super-additive on disjoint Finset unions**
(ferromagnetic). Direct wrapper of `log_partitionFunctionΛ_disjUnion_super_additive`. -/
theorem log_partitionFunctionΛ_latticeGraph_disjUnion_super_additive
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p)
      + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p)
    ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p) :=
  log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph d) hd p hf

/-- **ℤ^d `partitionFunctionΛ` respects Finset equality**. -/
theorem partitionFunctionΛ_latticeGraph_congr_finset
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h : Λ₁ = Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p :=
  partitionFunctionΛ_congr_finset (IsingModel.latticeGraph d) h p

end Ambient
end IsingModel
