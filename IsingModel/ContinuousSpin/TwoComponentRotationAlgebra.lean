import IsingModel.ContinuousSpin.TwoComponentRotation
import IsingModel.ContinuousSpin.TwoComponentGriffithsVI

/-!
# Algebraic identities for the (4.3.2) block rotation (GJ Theorem 4.7.1)

The coordinate, inner-product and potential identities relating the doubled
two-component configuration `(ξ, ξ')` to its §4.7 block `√2`-rotation, used in the
duplicate-variable proof of the second/third inequalities (4.7.6)–(4.7.8).

The per-site rotation `rotLin ![tᵢ, qᵢ, tᵢ', qᵢ']` produces the block coordinates
`(α, β, γ, δ) = ((t+t')/√2, (t−t')/√2, (q+q')/√2, (q'−q)/√2)`
(`rotLin_dCoord`).  In these coordinates:

* the doubled interaction is ferromagnetic,
  `ξᵢ·ξⱼ + ξᵢ'·ξⱼ' = αᵢαⱼ + βᵢβⱼ + γᵢγⱼ + δᵢδⱼ` (`doubled_dot_eq_rot`, GJ (4.3.5));
* the doubled potential is even plus ferromagnetic,
  `P(ξ) + P(ξ') = twoCompEvenPart − 4A·αβγδ` (`twoCompPotential_double_block`).

Both feed the doubled-rotated non-negativity `dRotInteraction_nonneg`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, (4.3.2), (4.3.5); §4.7, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Matrix

/-- The block `α`-coordinate `(t+t')/√2`. -/
noncomputable def bAlpha (t t' : ℝ) : ℝ := Real.sqrt 2 / 2 * (t + t')

/-- The block `β`-coordinate `(t−t')/√2`. -/
noncomputable def bBeta (t t' : ℝ) : ℝ := Real.sqrt 2 / 2 * (t - t')

/-- The block `γ`-coordinate `(q+q')/√2`. -/
noncomputable def bGamma (q q' : ℝ) : ℝ := Real.sqrt 2 / 2 * (q + q')

/-- The block `δ`-coordinate `(q'−q)/√2`. -/
noncomputable def bDelta (q q' : ℝ) : ℝ := Real.sqrt 2 / 2 * (q' - q)

/-- The single-site coordinate vector `![tᵢ, qᵢ, tᵢ', qᵢ']` of a doubled pair. -/
noncomputable def dCoord (ξ ξ' : VectorConfig ι) (i : ι) : Fin 4 → ℝ :=
  ![(ξ i).1, (ξ i).2, (ξ' i).1, (ξ' i).2]

/-- The rotated single site `rotLin (dCoord ξ ξ' i)` evaluated at each coordinate
gives the §4.7 block rotation `(α, β, γ, δ)`. -/
theorem rotLin_dCoord (ξ ξ' : VectorConfig ι) (i : ι) :
    rotLin (dCoord ξ ξ' i) 0 = bAlpha (ξ i).1 (ξ' i).1 ∧
    rotLin (dCoord ξ ξ' i) 1 = bBeta (ξ i).1 (ξ' i).1 ∧
    rotLin (dCoord ξ ξ' i) 2 = bGamma (ξ i).2 (ξ' i).2 ∧
    rotLin (dCoord ξ ξ' i) 3 = bDelta (ξ i).2 (ξ' i).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [rotLin, dCoord, rotMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      bAlpha, bBeta, bGamma, bDelta] <;> ring

/-- **GJ (4.3.5)**: the doubled inner product is the sum of the rotated inner
products, `tᵢtⱼ+qᵢqⱼ + tᵢ'tⱼ'+qᵢ'qⱼ' = αᵢαⱼ + βᵢβⱼ + γᵢγⱼ + δᵢδⱼ`. -/
theorem doubled_dot_eq_rot (ξ ξ' : VectorConfig ι) (i j : ι) :
    vDot ξ i j + vDot ξ' i j = dDot4 (fun k => rotLin (dCoord ξ ξ' k)) i j := by
  have hsq : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := sqrt2_half_mul_self
  obtain ⟨ha, hb, hc, hd⟩ := rotLin_dCoord ξ ξ' i
  obtain ⟨ha', hb', hc', hd'⟩ := rotLin_dCoord ξ ξ' j
  simp only [dDot4, Fin.sum_univ_four, ha, hb, hc, hd, ha', hb', hc', hd', vDot, vSpinT, vSpinQ,
    bAlpha, bBeta, bGamma, bDelta]
  linear_combination (-2 * ((ξ i).1 * (ξ j).1 + (ξ i).2 * (ξ j).2
    + (ξ' i).1 * (ξ' j).1 + (ξ' i).2 * (ξ' j).2)) * hsq

/-- **The doubled two-component potential in the block rotation** (GJ §4.7):
`P(t,q) + P(t',q') = twoCompEvenPart α β γ δ − 4A·αβγδ`, with `(α,β,γ,δ)` the
block `√2`-rotation of `(t, q, t', q')`.  The cross term is ferromagnetic for
`A ≥ 0`, matching `rotSiteDensity`. -/
theorem twoCompPotential_double_block (A σ t q t' q' : ℝ) :
    twoCompPotential A σ t q + twoCompPotential A σ t' q'
      = twoCompEvenPart A σ (bAlpha t t') (bBeta t t') (bGamma q q') (bDelta q q')
        - 4 * A * (bAlpha t t' * bBeta t t' * bGamma q q' * bDelta q q') := by
  have hc2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num
  have hc4 : (Real.sqrt 2 / 2) ^ 4 = 1 / 4 := by
    rw [show (Real.sqrt 2 / 2) ^ 4 = ((Real.sqrt 2 / 2) ^ 2) ^ 2 by ring, hc2]; norm_num
  have e1 : bAlpha t t' ^ 2 = (t + t') ^ 2 / 2 := by rw [bAlpha, mul_pow, hc2]; ring
  have e2 : bBeta t t' ^ 2 = (t - t') ^ 2 / 2 := by rw [bBeta, mul_pow, hc2]; ring
  have e3 : bGamma q q' ^ 2 = (q + q') ^ 2 / 2 := by rw [bGamma, mul_pow, hc2]; ring
  have e4 : bDelta q q' ^ 2 = (q' - q) ^ 2 / 2 := by rw [bDelta, mul_pow, hc2]; ring
  have ecross : bAlpha t t' * bBeta t t' * bGamma q q' * bDelta q q'
      = (t + t') * (t - t') * (q + q') * (q' - q) / 4 := by
    rw [bAlpha, bBeta, bGamma, bDelta]
    linear_combination ((t + t') * (t - t') * (q + q') * (q' - q)) * hc4
  simp only [twoCompPotential, twoCompEvenPart,
    show ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 from fun x => by ring]
  rw [e1, e2, e3, e4, ecross]
  ring

end IsingModel.ContinuousSpin
