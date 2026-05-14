import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLatticeSum

/-!
# Concrete partition/free-energy superadditivity wrappers

Narrow child module for concrete `latticeGraph` partition-function and
free-energy disjoint-union monotonicity / superadditivity wrappers. The theorem
names are the same as the former legacy declarations, but callers can now avoid
importing the monolithic concrete legacy module.
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

/-- **ℤ^d `|Λ| · freeEnergyΛ = log Z_Λ`** for nonempty `Λ`. -/
theorem card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) :
    (Λ.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty
    (IsingModel.latticeGraph d) hne p

/-- **ℤ^d weighted monotonicity of `freeEnergyΛ` on disjoint unions**
(ferromagnetic): `|Λ₁|·f_{Λ₁} ≤ |Λ₁ ∪ Λ₂|·f_{Λ₁ ∪ Λ₂}`. -/
theorem card_mul_freeEnergyΛ_latticeGraph_le_of_disjoint_union
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)}
    (hne₁ : Λ₁.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₁ p
      ≤ ((Λ₁ ∪ Λ₂).card : ℝ)
          * freeEnergyΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p := by
  classical
  exact card_mul_freeEnergyΛ_le_of_disjoint_union
    (IsingModel.latticeGraph d) hne₁ hd p hf

/-- **ℤ^d weighted super-additivity of `freeEnergyΛ` on disjoint unions**
(ferromagnetic). -/
theorem freeEnergyΛ_latticeGraph_weighted_super_additive_of_nonempty
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)}
    (hne₁ : Λ₁.Nonempty) (hne₂ : Λ₂.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₁ p
      + (Λ₂.card : ℝ) * freeEnergyΛ (IsingModel.latticeGraph d) Λ₂ p
    ≤ ((Λ₁ ∪ Λ₂).card : ℝ)
        * freeEnergyΛ (IsingModel.latticeGraph d) (Λ₁ ∪ Λ₂) p :=
  freeEnergyΛ_weighted_super_additive_of_nonempty
    (IsingModel.latticeGraph d) hne₁ hne₂ hd p hf

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
