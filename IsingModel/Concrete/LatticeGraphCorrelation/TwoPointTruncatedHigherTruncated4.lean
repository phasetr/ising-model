import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Trivial slices of the ℤ^d four-point truncated function

The statements here evaluate `truncated4Infinite (IsingModel.latticeGraph d) Λ p` on the
parameter slices where the truncation collapses, for an arbitrary exhaustion `Λ` of `Fin d → ℤ`.

At `β = 0` the value is `0`, for arbitrary couplings `J` and `h` and arbitrary sites.

At `J = 0` the spins are decoupled and each carries magnetization `Real.tanh (β * h)`, and the
truncation leaves `-2 * Real.tanh (β * h) ^ 4`. This is stated under `Ferromagnetic ⟨0, h, β⟩`,
which here amounts to `0 ≤ h` together with `0 < β`, once for four pairwise distinct sites and
once at the site tuple `i, i, k, l` in which the first two arguments coincide and `i`, `k`, `l`
are pairwise distinct; the coincidence changes the individual terms but not their combination.

Each is the specialization of the corresponding ambient statement to `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated4Infinite β=0 site-wise**: `= 0`. -/
theorem truncated4Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 :=
  truncated4Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k l

/-- **ℤ^d truncated4Infinite J=0 pairwise distinct site-wise**: `= -2·tanh(β·h)^4`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hik hil hjk hjl hkl

/-- **ℤ^d truncated4Infinite J=0 one-pair coincidence** (#745). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_one_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k l : Fin d → ℤ}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_one_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik hil hkl

end Ambient
end IsingModel
