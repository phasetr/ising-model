import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlation `J = 0` and empty-set wrappers

Instantiates the ambient correlation degeneracies at the ℤ^d lattice graph
`IsingModel.latticeGraph d`: the decoupled `J = 0` values along an exhaustion, and the
empty-subset normalization in Λ-level and along-exhaustion form. Each is a pass-through of
the corresponding abstract lemma.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0`** per stage (on-stage):
`A ⊆ Λ.volume n ⇒ = tanh(β·h)^|A|`. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_of_subset
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) {A : Finset (Fin d → ℤ)} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_of_subset (IsingModel.latticeGraph d) Λ h β hAn

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0` is eventually constant
at `tanh(β·h)^|A|`**. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β A


/-- **ℤ^d correlationΛ_empty = 1** per finite volume. -/
@[simp]
theorem correlationΛ_latticeGraph_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    correlationΛ (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationΛ_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d correlationAlongExhaustion_empty = 1** per stage. -/
@[simp]
theorem correlationAlongExhaustion_latticeGraph_empty
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p ∅ n = 1 :=
  correlationAlongExhaustion_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

end Ambient

end IsingModel
