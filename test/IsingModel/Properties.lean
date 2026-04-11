import IsingModel.Basic
import IsingModel.Hamiltonian
import IsingModel.GibbsMeasure

/-!
# Property tests for Ising model definitions

Exhaustive tests over small Fin types using `native_decide`.
These serve as regression tests for the computable parts of the definitions.
-/

set_option linter.hashCommand false

namespace IsingModel.Test

/-! ## Spin properties (exhaustive, decidable) -/

-- toSign_sq
example : ∀ s : Spin, s.toSign ^ 2 = 1 := by native_decide

-- flip_flip
example : ∀ s : Spin, s.flip.flip = s := by native_decide

-- flip_ne
example : ∀ s : Spin, s.flip ≠ s := by native_decide

-- toSign_flip
example : ∀ s : Spin, s.flip.toSign = -s.toSign := by native_decide

-- mul associativity-like: mul a (mul a b) = b
example : ∀ (a b : Spin), a.mul (a.mul b) = b := by native_decide

-- toSign_mul
example : ∀ (a b : Spin), (a.mul b).toSign = a.toSign * b.toSign := by native_decide

/-! ## spinProduct over ℤ (computable, Fin 3) -/

/-- Computable spin product in ℤ. -/
def spinProductZ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (σ : ι → Spin) : ℤ :=
  ∏ i ∈ A, (σ i).toSign

-- spinProductZ_sq: (σ^A)² = 1
example : ∀ (σ : Fin 3 → Spin) (A : Finset (Fin 3)),
    spinProductZ A σ ^ 2 = 1 := by native_decide

-- spinProductZ_empty: σ^∅ = 1
example : ∀ (σ : Fin 3 → Spin),
    spinProductZ ∅ σ = 1 := by native_decide

-- spinProductZ singleton
example : ∀ (σ : Fin 3 → Spin) (i : Fin 3),
    spinProductZ {i} σ = (σ i).toSign := by native_decide

-- spinProductZ_mul: σ^A · σ^C = σ^{AΔC}
example : ∀ (σ : Fin 3 → Spin) (A C : Finset (Fin 3)),
    spinProductZ A σ * spinProductZ C σ = spinProductZ (symmDiff A C) σ := by native_decide

/-! ## Config flip properties (Fin 2) -/

-- flipAt is involution
example : ∀ (j : Fin 2) (σ : Fin 2 → Spin),
    (Config.flipAt j σ).flipAt j = σ := by native_decide

-- flipAt changes the configuration
example : ∀ (j : Fin 2) (σ : Fin 2 → Spin),
    Config.flipAt j σ ≠ σ := by native_decide

-- Spin product negated by flipAt
example : ∀ (A : Finset (Fin 2)) (j : Fin 2) (σ : Fin 2 → Spin),
    j ∈ A → spinProductZ A (Config.flipAt j σ) = -spinProductZ A σ := by native_decide

end IsingModel.Test
