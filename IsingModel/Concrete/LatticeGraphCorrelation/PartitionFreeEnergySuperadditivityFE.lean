import IsingModel.AmbientLatticeSum
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d freeEnergyΛ superadditivity wrappers

Narrow child module for three ℤ^d Λ-layer freeEnergyΛ
superadditivity wrappers extracted from
`PartitionFreeEnergySuperadditivity.lean`:

* `card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty`,
* `card_mul_freeEnergyΛ_latticeGraph_le_of_disjoint_union`,
* `freeEnergyΛ_latticeGraph_weighted_super_additive_of_nonempty`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.{card_mul_freeEnergyΛ_*,freeEnergyΛ_weighted_super_additive_*}`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `PartitionFreeEnergySuperadditivity`
declarations.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
