import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# Pseudo-mass from parameters: general properties

Exhaustion independence, h-symmetry, positivity/zero tests, and sandwich bounds.
-/

namespace IsingModel

open Set Real Filter

/-- **`pseudoMassFromParamsAtPair` independence of exhaustion for
ferromagnetic params**: `correlationInfinite` is exhaustion-independent
under ferromagnetic hypothesis, hence so is the bridge. -/
theorem pseudoMassFromParamsAtPair_indep_exhaustion {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassFromParamsAtPair hα hr d Λ' p x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  exact Ambient.correlationInfinite_indep_exhaustion
    (IsingModel.latticeGraph d) Λ Λ' p hf {x, z}

/-- **`pseudoMassFromParamsAtPair` h-symmetry under `h → -h` for distinct
pairs**: `|{x, z}| = 2` is even, so `correlationInfinite` is unchanged
under `h ↦ -h`, hence the bridge is too. -/
theorem pseudoMassFromParamsAtPair_neg_h_distinct {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J h β : ℝ) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, -h, β⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, h, β⟩ : IsingParams ℝ) x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  have heven : Even (({x, z} : Finset (Fin d → ℤ)).card) := by
    rw [Finset.card_pair hxz]
    decide
  exact Ambient.correlationInfinite_neg_h_of_even_card
    (IsingModel.latticeGraph d) Λ J h β {x, z} heven

/-- **`pseudoMassFromParamsAtPair = 0 ↔ correlation ∉ Ioo 0 2`**: lifted from
`pseudoMassExt_eq_zero_iff`. -/
theorem pseudoMassFromParamsAtPair_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∉ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_eq_zero_iff hα hr _

/-- **`pseudoMassFromParamsAtPair > 0 ↔ correlation ∈ Ioo 0 2`**: lifted from
`pseudoMassExt_pos_iff`. -/
theorem pseudoMassFromParamsAtPair_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_pos_iff hα hr _

/-- **`pseudoMassFromParamsAtPair` sandwich**: if `c_min ≤ correlation ≤ c_max`
all in `Ioo 0 2`, then `pseudoMassExt c_max ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt c_min`.

Both bounds come from the strict anti-monotonicity of `pseudoMassExt` on
`Ioo 0 2` (`pseudoMassExt_strictAntiOn`), split on whether the correlation
attains the bound: on equality the two sides coincide, otherwise the
inequality is strict. Useful for the §17.5 Lemma 17.5.2 capstone. -/
theorem pseudoMassFromParamsAtPair_sandwich_of_corr_mem {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min := by
  unfold pseudoMassFromParamsAtPair
  constructor
  · by_cases heq :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_max
    · rw [heq]
    · exact le_of_lt
        (pseudoMassExt_strictAntiOn hα hr hcorr hc_max (lt_of_le_of_ne hle heq))
  · by_cases heq :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_min
    · rw [heq]
    · exact le_of_lt
        (pseudoMassExt_strictAntiOn hα hr hc_min hcorr
          (lt_of_le_of_ne hge (Ne.symm heq)))

end IsingModel
