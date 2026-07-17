import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-induced spinProduct and `J = 0` bot wrappers

Narrow child module for five ℤ^d Λ-induced wrappers extracted from
`EnergyClosedForms.lean`:

* `partitionFunction_eq_bot_at_J_zero_latticeGraph`,
* `correlation_eq_bot_at_J_zero_latticeGraph`,
* `spinProduct_singleton_latticeGraph`,
* `spinProduct_union_latticeGraph`,
* `spinProduct_sq_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_eq_bot_at_J_zero direct** (Λ-induced):
`Z_G ⟨0, h, β⟩ = Z_⊥ ⟨0, h, β⟩`. Thin pass-through of
`IsingModel.partitionFunction_eq_bot_at_J_zero`. -/
theorem partitionFunction_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d correlation_eq_bot_at_J_zero direct** (Λ-induced):
`⟨σ^A⟩_G = ⟨σ^A⟩_⊥` at `J = 0`. Thin pass-through of
`IsingModel.correlation_eq_bot_at_J_zero`. -/
theorem correlation_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d spinProduct_singleton direct** (Λ-induced):
`spinProduct {i} σ = sign(σ_i)`. Thin pass-through of
`IsingModel.spinProduct_singleton`. -/
theorem spinProduct_singleton_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (i : (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct ({i} : Finset (↑Λ : Type _)) σ
      = ((σ i).toSign : ℝ) :=
  IsingModel.spinProduct_singleton i σ

/-- **ℤ^d spinProduct_union direct** (Λ-induced): for disjoint
`A, B : Finset (↑Λ)`, `spinProduct (A ∪ B) = spinProduct A · spinProduct B`.
Thin pass-through of `IsingModel.spinProduct_union`. -/
theorem spinProduct_union_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {A B : Finset (↑Λ : Type _)} (hAB : Disjoint A B)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct (A ∪ B) σ
      = IsingModel.spinProduct A σ * IsingModel.spinProduct B σ :=
  IsingModel.spinProduct_union hAB σ

/-- **ℤ^d spinProduct_sq direct** (Λ-induced):
`(spinProduct A σ)^2 = 1` since each factor is `±1`. Thin pass-through
of `IsingModel.spinProduct_sq`. -/
theorem spinProduct_sq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (A : Finset (↑Λ : Type _))
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.spinProduct A σ ^ 2 = 1 :=
  IsingModel.spinProduct_sq A σ

end Ambient
end IsingModel
