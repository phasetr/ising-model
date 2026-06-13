import IsingModel.ContinuousSpin.TwoComponentRotation
import IsingModel.ContinuousSpin.TwoComponentGriffithsVI

/-!
# Algebraic identities for the (4.3.2) rotation (GJ Theorem 4.7.1)

The coordinate and inner-product identities relating the doubled two-component
configuration `(ξ, ξ')` to its rotation, used in the duplicate-variable proof of
the second/third inequalities (4.7.6)–(4.7.8).  The per-site rotation
`rotLin ![tᵢ, qᵢ, tᵢ', qᵢ']` produces `(α, β, γ, δ) = (phi4Alpha, phi4Beta,
phi4Gamma, twoCompDelta)`, and the doubled interaction is ferromagnetic in the
rotated coordinates:
`ξᵢ·ξⱼ + ξᵢ'·ξⱼ' = αᵢαⱼ + βᵢβⱼ + γᵢγⱼ + δᵢδⱼ` (GJ (4.3.5)).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, (4.3.2), (4.3.5); §4.7, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Matrix

/-- The single-site coordinate vector `![tᵢ, qᵢ, tᵢ', qᵢ']` of a doubled pair. -/
noncomputable def dCoord (ξ ξ' : VectorConfig ι) (i : ι) : Fin 4 → ℝ :=
  ![(ξ i).1, (ξ i).2, (ξ' i).1, (ξ' i).2]

/-- The rotated single site `rotLin (dCoord ξ ξ' i)` evaluated at each coordinate
gives the §4.3 rotation `(phi4Alpha, phi4Beta, phi4Gamma, twoCompDelta)`. -/
theorem rotLin_dCoord (ξ ξ' : VectorConfig ι) (i : ι) :
    rotLin (dCoord ξ ξ' i) 0 = phi4Alpha (ξ i).1 (ξ i).2 (ξ' i).1 (ξ' i).2 ∧
    rotLin (dCoord ξ ξ' i) 1 = phi4Beta (ξ i).1 (ξ i).2 (ξ' i).1 (ξ' i).2 ∧
    rotLin (dCoord ξ ξ' i) 2 = phi4Gamma (ξ i).1 (ξ i).2 (ξ' i).1 (ξ' i).2 ∧
    rotLin (dCoord ξ ξ' i) 3 = twoCompDelta (ξ i).1 (ξ i).2 (ξ' i).1 (ξ' i).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [rotLin, dCoord, rotMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      phi4Alpha, phi4Beta, phi4Gamma, twoCompDelta, phi4Delta] <;> ring

/-- **GJ (4.3.5)**: the doubled inner product is the sum of the rotated inner
products, `tᵢtⱼ+qᵢqⱼ + tᵢ'tⱼ'+qᵢ'qⱼ' = αᵢαⱼ + βᵢβⱼ + γᵢγⱼ + δᵢδⱼ`. -/
theorem doubled_dot_eq_rot (ξ ξ' : VectorConfig ι) (i j : ι) :
    vDot ξ i j + vDot ξ' i j = dDot4 (fun k => rotLin (dCoord ξ ξ' k)) i j := by
  obtain ⟨ha, hb, hc, hd⟩ := rotLin_dCoord ξ ξ' i
  obtain ⟨ha', hb', hc', hd'⟩ := rotLin_dCoord ξ ξ' j
  simp only [dDot4, Fin.sum_univ_four, ha, hb, hc, hd, ha', hb', hc', hd', vDot, vSpinT, vSpinQ,
    phi4Alpha, phi4Beta, phi4Gamma, twoCompDelta, phi4Delta]
  ring

end IsingModel.ContinuousSpin
