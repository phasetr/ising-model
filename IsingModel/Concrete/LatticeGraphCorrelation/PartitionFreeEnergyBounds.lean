import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d lower bounds on the partition function on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the ferromagnetic
lower bounds on the partition function: it is at least `1` and at least `2 ^ |Λ|`, and its
logarithm is nonnegative and at least `|Λ| * log 2`. Every statement here assumes the
ferromagnetic hypothesis on the parameter record, and none assumes `Λ` nonempty.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

end Ambient

end IsingModel
