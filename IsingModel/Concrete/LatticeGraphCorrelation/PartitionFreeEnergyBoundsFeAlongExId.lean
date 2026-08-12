import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d free-energy density as a normalised logarithm, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the identification of the free-energy density with the
logarithm of the partition function scaled by the inverse stage volume, in the `Finset.card`
normalisation, together with its nonnegativity. The identity carries no hypothesis; the
nonnegativity assumes the ferromagnetic hypothesis on the parameter record and a nonempty stage
volume.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d `freeEnergyAlongExhaustion = ((Λ.volume n).card)⁻¹ · log Z_n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion ≥ 0`** per stage (ferromagnetic,
nonempty stage, any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

end Ambient

end IsingModel
