import IsingModel.ContinuousSpin.TwoComponentMultiIntegrable
import IsingModel.ContinuousSpin.TwoComponentGriffiths

/-!
# Integrability of a general monomial against the two-component Gibbs weight

For the duplicate-variable proof of the second/third inequalities of GJ Theorem
4.7.1 (4.7.6)–(4.7.8), the GKS-II doubling identity needs the integrability of a
*general* monomial `∏ᵢ tᵢ^{aᵢ} qᵢ^{bᵢ}` against the two-component Gibbs weight.
The proof mirrors `integrable_vectorWeight`: the uniform AM-GM exponent bound
dominates `vectorWeight` by `exp K · ∏ᵢ modSpinDensity c A (ξ i)`, and the extra
monomial factor is absorbed into a product of integrable monomial-weighted
modified single-spin densities.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

variable {ι : Type*}

/-- A general two-component spin monomial `∏ᵢ tᵢ^{aᵢ} qᵢ^{bᵢ}`. -/
noncomputable def genMonomial [Fintype ι] (a b : ι → ℕ) (ξ : VectorConfig ι) : ℝ :=
  ∏ i, (ξ i).1 ^ a i * (ξ i).2 ^ b i

/-- A general two-component spin monomial is continuous. -/
theorem continuous_genMonomial [Fintype ι] (a b : ι → ℕ) : Continuous (genMonomial a b) := by
  unfold genMonomial; fun_prop

/-- **Integrability of the absolute monomial-weighted modified single-spin density**:
`ξ ↦ |t|ᵃ|q|ᵇ·modSpinDensity c A ξ` is integrable for `A > 0`. -/
theorem integrable_abs_pow_mul_modSpinDensity {c A : ℝ} (hA : 0 < A) (a b : ℕ) :
    Integrable (fun ξ : ℝ × ℝ => |ξ.1| ^ a * |ξ.2| ^ b * modSpinDensity c A ξ) := by
  refine ((integrable_pow_mul_singleSpinDensity (A := A) (σ := -c) hA a b).norm).congr
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hmod : modSpinDensity c A ξ = singleSpinDensity A (-c) ξ := by
    simp only [modSpinDensity, singleSpinDensity]; ring_nf
  have hpos : (0 : ℝ) < singleSpinDensity A (-c) ξ := Real.exp_pos _
  simp only [hmod, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hpos]

/-- **Integrability of a general monomial against the two-component Gibbs weight**
for `A > 0`. -/
theorem integrable_genMonomial_mul_vectorWeight [Fintype ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] {A : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A) (a b : ι → ℕ) :
    Integrable (fun ξ : VectorConfig ι => genMonomial a b ξ * vectorWeight G A σ J h1 h2 β ξ) := by
  obtain ⟨K, c, hbound⟩ := exists_vectorWeight_exponent_bound G A σ J h1 h2 β
  have hdom : Integrable (fun ξ : VectorConfig ι =>
      Real.exp K * ∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i * modSpinDensity c A (ξ i))) := by
    refine Integrable.const_mul ?_ _
    rw [volume_pi]
    exact Integrable.fintype_prod fun i => integrable_abs_pow_mul_modSpinDensity hA (a i) (b i)
  refine hdom.mono'
    ((continuous_genMonomial a b).mul
      (continuous_vectorWeight G A σ J h1 h2 β)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (vectorWeight_pos G A σ J h1 h2 β ξ)]
  have habs : |genMonomial a b ξ| = ∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i) := by
    rw [genMonomial, Finset.abs_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [abs_mul, abs_pow, abs_pow]
  rw [habs]
  have hwle : vectorWeight G A σ J h1 h2 β ξ
      ≤ Real.exp K * ∏ i, modSpinDensity c A (ξ i) := by
    have hprod_eq : (∏ i, modSpinDensity c A (ξ i))
        = Real.exp (∑ i, (c * normSq ξ i - A * (normSq ξ i) ^ 2)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => rfl
    rw [hprod_eq, ← Real.exp_add, vectorWeight]
    exact Real.exp_le_exp.mpr (hbound ξ)
  calc (∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i)) * vectorWeight G A σ J h1 h2 β ξ
      ≤ (∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i))
          * (Real.exp K * ∏ i, modSpinDensity c A (ξ i)) :=
        mul_le_mul_of_nonneg_left hwle (Finset.prod_nonneg fun i _ => by positivity)
    _ = Real.exp K * ∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i * modSpinDensity c A (ξ i)) := by
        rw [show (∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i * modSpinDensity c A (ξ i)))
            = (∏ i, (|(ξ i).1| ^ a i * |(ξ i).2| ^ b i)) * ∏ i, modSpinDensity c A (ξ i)
          from Finset.prod_mul_distrib]
        ring

end IsingModel.ContinuousSpin
