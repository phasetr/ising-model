import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlation h_zero (Z₂ symmetry) wrappers

Narrow child module for five ℤ^d Z₂ symmetry / `correlation*_latticeGraph_*_h_zero`
wrappers (`correlationΛ_odd_vanish_h_zero`,
`correlationAlongExhaustion_h_zero`,
`correlationInfinite_cubicExhaustion_h_zero`,
`correlationInfinite_h_zero`,
`correlationAlongExhaustion_any_h_zero`). Each wrapper is a thin
pass-through to the corresponding ambient `correlation*_*_h_zero`
lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationΛ`**:
odd-cardinality spin product vanishes at h=0. -/
theorem correlationΛ_latticeGraph_odd_vanish_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A = 0 :=
  correlationΛ_odd_vanish_h_zero (IsingModel.latticeGraph d) Λ J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`** stage-wise. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A n = 0 :=
  correlationAlongExhaustion_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd n

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationInfinite`**:
`correlationInfinite ⟨J, 0, β⟩ A = 0` for any `A` of odd cardinality. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A = 0 :=
  correlationInfinite_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationInfinite`** (any-Exhaustion):
`correlationInfinite ⟨J, 0, β⟩ A = 0` for any `A` of odd cardinality. -/
theorem correlationInfinite_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A = 0 :=
  correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`**
(any-Exhaustion, stage-wise). -/
theorem correlationAlongExhaustion_latticeGraph_any_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A n = 0 :=
  correlationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β A hodd n

end Ambient
end IsingModel
