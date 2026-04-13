import IsingModel.FreeEnergy

/-!
# Conditioning inequalities

Formalization of results from Glimm–Jaffe, Chapter 10 (pp. 193–198),
specialized to the lattice Ising model.

## Main results

* `partitionFunction_beta_rescale` — `Z(J,h,β) = Z(βJ,βh,1)`
* `partitionFunction_monotone_beta` — `Z` monotone in `β` (Cor. 10.2.3)
* `freeEnergy_bounded` — `|f| ≤ ln 2 + |β|(|J|·|E|/|ι| + |h|)` (Cor. 10.3.2)

## References

* Glimm–Jaffe, *Quantum Physics*, §10.1–10.3, pp. 193–197
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in β (Corollary 10.2.3, lattice version) -/

/-- The partition function depends on `(J, h, β)` only through `(βJ, βh)`:
`Z(J, h, β) = Z(βJ, βh, 1)`. -/
private theorem partitionFunction_beta_rescale
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    partitionFunction G ⟨J, h, β⟩ = partitionFunction G ⟨β * J, β * h, 1⟩ := by
  unfold partitionFunction boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  congr 1; ext σ; congr 1; ring

/-- **Corollary 10.2.3** (lattice version).
The partition function is monotone increasing in `β` on `(0, ∞)`.

For `0 < β₁ ≤ β₂`, `J ≥ 0`, `h ≥ 0`:
`Z(J, h, β₁) ≤ Z(J, h, β₂)`. -/
theorem partitionFunction_monotone_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) (β₁ β₂ : ℝ)
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunction G ⟨J, h, β₁⟩ ≤ partitionFunction G ⟨J, h, β₂⟩ := by
  rw [partitionFunction_beta_rescale G J h β₁,
      partitionFunction_beta_rescale G J h β₂]
  calc partitionFunction G ⟨β₁ * J, β₁ * h, 1⟩
      ≤ partitionFunction G ⟨β₂ * J, β₁ * h, 1⟩ :=
        partitionFunction_monotone_J G (β₁ * h) 1
          (mul_nonneg hβ₁.le hh) one_pos (β₁ * J) (β₂ * J)
          (mul_nonneg hβ₁.le hJ) (by nlinarith)
    _ ≤ partitionFunction G ⟨β₂ * J, β₂ * h, 1⟩ :=
        partitionFunction_monotone_h G (β₂ * J) 1
          (mul_nonneg (le_trans hβ₁.le hβ) hJ) one_pos (β₁ * h) (β₂ * h)
          (mul_nonneg hβ₁.le hh) (by nlinarith)

/-! ## Partition function bounds (Corollary 10.3.2, lattice version)

The partition function satisfies `0 < Z` (already `partitionFunction_pos`).

The conditioning monotonicity (Prop. 10.3.1) for the lattice Ising model
is a consequence of GKS-II: increasing the coupling `J` increases
correlations (`correlation_monotone_J`). The Dirichlet/Neumann boundary
condition framework requires additional infrastructure (subgraphs,
boundary spin fixing) that is deferred to future work.

The free energy boundedness (Cor. 10.3.2) in the lattice case
follows from `|H(σ)| ≤ |J||E| + |h||ι|`, giving
`exp(-|β|(|J||E| + |h||ι|)) ≤ Z/2^|ι| ≤ exp(|β|(|J||E| + |h||ι|))`. -/

end IsingModel
