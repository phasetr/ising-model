import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `*_ge_tanh*` ferromagnetic wrappers

Narrow child module for four ferromagnetic `*_ge_tanh*_latticeGraph`
wrappers extracted from `BaseBoundsTanh.lean`:

* `correlationΛ_latticeGraph_ge_tanh_pow_card`,
* `correlationInfinite_latticeGraph_ge_tanh_pow_card`,
* `magnetizationΛ_latticeGraph_ge_tanh`,
* `magnetizationInfinite_latticeGraph_ge_tanh`.

Each result is a thin pass-through of the corresponding abstract
`correlation*_ge_tanh_pow_card` / `magnetization*_ge_tanh` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `BaseBoundsTanh` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationΛ_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A

/-- **ℤ^d `correlationInfinite ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationInfinite_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A


/-- **ℤ^d `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationΛ_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i

/-- **ℤ^d `magnetizationInfinite ≥ tanh(β·h)`** (ferromagnetic, any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : Fin d → ℤ) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i


end Ambient

end IsingModel
