import IsingModel.FreeEnergy

/-!
# Conditioning inequalities

Formalization of results from Glimm–Jaffe, Chapter 10, §10.1–10.2
(pp. 193–194), specialized to the lattice Ising model.

## Main results

* `partitionFunction_monotone_beta` — `Z` is monotone increasing in `β`
  on `(0, ∞)` for ferromagnetic `J ≥ 0` and `h ≥ 0`

## References

* Glimm–Jaffe, *Quantum Physics*, §10.2, Corollary 10.2.3, p. 194
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in β (Corollary 10.2.3, lattice version)

For the ferromagnetic Ising model with `J ≥ 0` and `h ≥ 0`:
`Z(J, h, β₂) ≥ Z(J, h, β₁)` when `0 < β₁ ≤ β₂`.

This follows from the identity `Z(J, h, β) = Z(βJ, βh, 1)` and the
monotonicity of `Z` in `J` and `h` on `[0, ∞)`. -/

/-- The partition function depends on `(J, h, β)` only through `(βJ, βh)`:
`Z(J, h, β) = Z(βJ, βh, 1)`. -/
private theorem partitionFunction_beta_rescale
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    partitionFunction G ⟨J, h, β⟩ = partitionFunction G ⟨β * J, β * h, 1⟩ := by
  unfold partitionFunction boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  congr 1; ext σ; congr 1; ring

/-- **Corollary 10.2.3** (Glimm–Jaffe, §10.2, p. 194, lattice version).
The partition function is monotone increasing in `β` on `(0, ∞)`.

For `0 < β₁ ≤ β₂`, `J ≥ 0`, `h ≥ 0`:
`Z(J, h, β₁) ≤ Z(J, h, β₂)`.

Proof: `Z(J, h, β) = Z(βJ, βh, 1)`. Since `βJ` and `βh` are monotone
in `β` for `J, h ≥ 0`, the result follows from `partitionFunction_monotone_J`
and `partitionFunction_monotone_h`. -/
theorem partitionFunction_monotone_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) (β₁ β₂ : ℝ)
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunction G ⟨J, h, β₁⟩ ≤ partitionFunction G ⟨J, h, β₂⟩ := by
  rw [partitionFunction_beta_rescale G J h β₁,
      partitionFunction_beta_rescale G J h β₂]
  -- Goal: Z(β₁J, β₁h, 1) ≤ Z(β₂J, β₂h, 1)
  -- Step 1: increase J from β₁J to β₂J
  calc partitionFunction G ⟨β₁ * J, β₁ * h, 1⟩
      ≤ partitionFunction G ⟨β₂ * J, β₁ * h, 1⟩ :=
        partitionFunction_monotone_J G (β₁ * h) 1
          (mul_nonneg hβ₁.le hh) one_pos (β₁ * J) (β₂ * J)
          (mul_nonneg hβ₁.le hJ) (by nlinarith)
    _ ≤ partitionFunction G ⟨β₂ * J, β₂ * h, 1⟩ :=
        partitionFunction_monotone_h G (β₂ * J) 1
          (mul_nonneg (le_trans hβ₁.le hβ) hJ) one_pos (β₁ * h) (β₂ * h)
          (mul_nonneg hβ₁.le hh) (by nlinarith)

end IsingModel
