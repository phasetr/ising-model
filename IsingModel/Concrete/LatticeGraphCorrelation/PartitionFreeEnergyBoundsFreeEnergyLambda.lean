import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Λ-layer `freeEnergyΛ` identity/nonneg wrappers

Narrow child module for three ℤ^d Λ-layer
`freeEnergyΛ_latticeGraph_*` identity / nonneg wrappers extracted from
`PartitionFreeEnergyBounds.lean`:

* `freeEnergyΛ_latticeGraph_eq_inv_card_mul_log`,
* `freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log`,
* `freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic`.

Each result is a thin pass-through of the ambient
`Ambient.freeEnergyΛ_*` lemma at `G := IsingModel.latticeGraph d`.
The theorem names are unchanged from the former
`PartitionFreeEnergyBounds` declarations.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d `freeEnergyΛ = |↑Λ|⁻¹ · log Z_Λ`**. -/
theorem freeEnergyΛ_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ = (Λ.card)⁻¹ · log Z_Λ`** (Finset-card form). -/
theorem freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Λ.card : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ ≥ 0`** (ferromagnetic, nonempty `Λ`). -/
theorem freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

end Ambient

end IsingModel
