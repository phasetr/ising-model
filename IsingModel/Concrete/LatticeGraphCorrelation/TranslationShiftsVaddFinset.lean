import IsingModel.Concrete.IntLattice

/-!
# ℤ^d Λ-direct vaddFinset_eq translation wrappers

Narrow child module for four ℤ^d
`*Λ_latticeGraph_vaddFinset_eq` translation wrappers extracted from
`TranslationShifts.lean`:

* `correlationΛ_latticeGraph_vaddFinset_eq`,
* `partitionFunctionΛ_latticeGraph_vaddFinset_eq`,
* `freeEnergyΛ_latticeGraph_vaddFinset_eq`,
* `log_partitionFunctionΛ_latticeGraph_vaddFinset_eq`.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationΛ translation invariance**:
`⟨σ^{vadd A}⟩_{t +ᵥ Λ}(p) = ⟨σ^A⟩_Λ(p)` on ℤ^d. -/
theorem correlationΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p A

/-- **ℤ^d partitionFunctionΛ translation invariance**:
`Z_{t +ᵥ Λ}(p) = Z_Λ(p)` on ℤ^d. -/
theorem partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d freeEnergyΛ translation invariance**:
`f_{t +ᵥ Λ}(p) = f_Λ(p)` on ℤ^d. -/
theorem freeEnergyΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d log_partitionFunctionΛ translation invariance**:
`log Z_{t +ᵥ Λ}(p) = log Z_Λ(p)` on ℤ^d. -/
theorem log_partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        (vaddFinset t Λ) p)
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) := by
  rw [partitionFunctionΛ_latticeGraph_vaddFinset_eq d t Λ p]

end Ambient
end IsingModel
