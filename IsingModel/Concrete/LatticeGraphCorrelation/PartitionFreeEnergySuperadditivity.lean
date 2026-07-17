import IsingModel.AmbientLatticeSum.LambdaSuperadditivity
import IsingModel.Lattice

/-!
# Concrete partition/free-energy superadditivity wrappers

Narrow child module for concrete `latticeGraph` partition-function and
free-energy disjoint-union monotonicity / superadditivity wrappers. The theorem
names are the same as the former declarations, but callers can now avoid
importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d partition/free-energy disjoint-union wrappers -/

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

/-! ## Moved: freeEnergyΛ superadditivity wrappers

The three wrappers
`card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty`,
`card_mul_freeEnergyΛ_latticeGraph_le_of_disjoint_union`,
`freeEnergyΛ_latticeGraph_weighted_super_additive_of_nonempty` now live
in `PartitionFreeEnergySuperadditivityFE.lean`. -/


/-- **ℤ^d `partitionFunctionΛ` respects Finset equality**. -/
theorem partitionFunctionΛ_latticeGraph_congr_finset
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h : Λ₁ = Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ₁ p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ₂ p :=
  partitionFunctionΛ_congr_finset (IsingModel.latticeGraph d) h p

/-! ## Moved: partitionFunctionΛ disjoint_union ≤ wrappers

The two wrappers
`log_partitionFunctionΛ_latticeGraph_le_of_disjoint_union`,
`partitionFunctionΛ_latticeGraph_le_of_disjoint_union` now live in
`PartitionFreeEnergySuperadditivityDisjointUnion.lean`. -/


end Ambient
end IsingModel
