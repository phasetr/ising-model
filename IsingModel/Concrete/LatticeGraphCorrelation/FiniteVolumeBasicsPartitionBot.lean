import IsingModel.FreeEnergy.SubgraphBounds

/-!
# ℤ^d `partitionFunction_bot_latticeGraph_*` wrappers

Narrow child module for three ℤ^d `partitionFunction_bot_latticeGraph_*`
wrappers extracted from `FiniteVolumeBasics.lean`:

* `partitionFunction_bot_latticeGraph`,
* `partitionFunction_bot_latticeGraph_ge_one`,
* `partitionFunction_bot_latticeGraph_ge_two_pow_card`.

Each result is a thin pass-through of the corresponding abstract
`IsingModel.partitionFunction_bot_*` lemma on the `⊥` subgraph of
the Λ-induced graph at `IsingModel.latticeGraph d`. The theorem
names are unchanged from the former `FiniteVolumeBasics` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunction` of `⊥` at Λ**: closed form
`Z_⊥ = (2 cosh(βh))^|Λ|`. -/
theorem partitionFunction_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p
      = (2 * Real.cosh (p.β * p.h)) ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.partitionFunction_bot (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 1`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (1 : ℝ) ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_one (ι := (↑Λ : Type _)) p

/-- **ℤ^d `partitionFunction (⊥) ≥ 2^|Λ|`** at Λ-induced subgraph. -/
theorem partitionFunction_bot_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    (2 : ℝ) ^ Fintype.card (↑Λ : Type _)
      ≤ IsingModel.partitionFunction (⊥ : SimpleGraph (↑Λ : Type _)) p :=
  IsingModel.partitionFunction_bot_ge_two_pow_card (ι := (↑Λ : Type _)) p

end Ambient
end IsingModel
