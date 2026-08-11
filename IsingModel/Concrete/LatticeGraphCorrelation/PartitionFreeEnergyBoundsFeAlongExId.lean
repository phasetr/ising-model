import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d free-energy density as a normalised logarithm, along an exhaustion

Instantiates at `IsingModel.latticeGraph d`, along an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and at a fixed stage `n`, the identification of the free-energy density with the
logarithm of the partition function scaled by the inverse stage volume, in the `Fintype.card`
normalisation and in the `Finset.card` normalisation, together with its nonnegativity. The
identities carry no hypothesis; the nonnegativity assumes the ferromagnetic hypothesis on the
parameter record and a nonempty stage volume.
-/

namespace IsingModel

namespace Ambient

/-- **ℤ^d `freeEnergyAlongExhaustion = |↑(Λ_n)|⁻¹ · log Z_n`** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p n

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

/-- **ℤ^d `freeEnergyAlongExhaustion` as `log Z / card`** (any-Exhaustion).

Restates `freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log` above:
the two conclusions are the same proposition, and the declarations differ only
in the ambient lemma they delegate to. The genuinely different cardinality
spelling is `freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log`,
which uses `(Λ.volume n).card` in place of `Fintype.card`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_log_div_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card
    (IsingModel.latticeGraph d) Λ p n

end Ambient

end IsingModel
