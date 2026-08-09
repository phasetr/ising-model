import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d free-energy density as a normalised logarithm, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the identification
of the free-energy density with the logarithm of the partition function scaled by the inverse
volume, in the `Fintype.card` normalisation and in the `Finset.card` normalisation, together
with its nonnegativity. The identities carry no hypothesis; the nonnegativity assumes the
ferromagnetic hypothesis on the parameter record and `Λ` nonempty.
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
