import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d sharp cosh lower bounds on the partition function on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the sharpened
ferromagnetic lower bound `(2 * cosh (β * h)) ^ |Λ|` on the partition function and its
logarithmic form `|Λ| * log (2 * cosh (β * h))`. Each statement assumes the ferromagnetic
hypothesis on the parameter record, and none assumes `Λ` nonempty.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d partitionFunctionΛ ≥ (2 cosh βh)^|Λ|** (sharp, ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d sharp log Z_Λ bound**: `|Λ|·log(2 cosh βh) ≤ log Z_Λ` (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

end Ambient

end IsingModel
