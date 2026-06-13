import IsingModel.ContinuousSpin.TwoComponentMonomialIntegrable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The GKS-II doubling identity (GJ Theorem 4.7.1, second/third inequalities)

The Ginibre duplicate-variable reduction underlying the second and third
inequalities of GJ Theorem 4.7.1 (4.7.6)–(4.7.8), pp. 70–71.  For a positive
integrable weight `W` and observables `F, G` with the appropriate integrabilities,
`(∫ W)·(∫ F·G·W) − (∫ F·W)·(∫ G·W)
  = ½·∫∫ (F(ξ)−F(ξ'))·(G(ξ)−G(ξ'))·W(ξ)·W(ξ')`
(`doubling_identity`).  Consequently, if the doubled integral is non-negative,
then `⟨F·G⟩ ≥ ⟨F⟩·⟨G⟩` (`vectorExpectation_doubling_le`), the truncated-pair
positivity at the heart of (4.7.6)–(4.7.7).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- **The GKS-II doubling identity** for a weight `W` and observables `F, G` with
the appropriate integrabilities. -/
theorem doubling_identity {W F G : VectorConfig ι → ℝ}
    (hW : Integrable W) (hFW : Integrable (fun ξ => F ξ * W ξ))
    (hGW : Integrable (fun ξ => G ξ * W ξ))
    (hFGW : Integrable (fun ξ => F ξ * G ξ * W ξ)) :
    (∫ ξ, W ξ) * (∫ ξ, F ξ * G ξ * W ξ) - (∫ ξ, F ξ * W ξ) * (∫ ξ, G ξ * W ξ)
      = (1 / 2) * ∫ z : VectorConfig ι × VectorConfig ι,
          (F z.1 - F z.2) * (G z.1 - G z.2) * W z.1 * W z.2 := by
  have hvol : (volume : Measure (VectorConfig ι × VectorConfig ι))
      = (volume : Measure (VectorConfig ι)).prod volume := rfl
  -- The four product-form integrals via Fubini separation.
  have e1 : (∫ z : VectorConfig ι × VectorConfig ι, F z.1 * G z.1 * W z.1 * W z.2)
      = (∫ ξ, F ξ * G ξ * W ξ) * ∫ ξ, W ξ := by
    rw [hvol, ← integral_prod_mul (fun ξ => F ξ * G ξ * W ξ) W]
  have e2 : (∫ z : VectorConfig ι × VectorConfig ι, F z.1 * W z.1 * (G z.2 * W z.2))
      = (∫ ξ, F ξ * W ξ) * ∫ ξ, G ξ * W ξ := by
    rw [hvol, ← integral_prod_mul (fun ξ => F ξ * W ξ) (fun ξ => G ξ * W ξ)]
  have e3 : (∫ z : VectorConfig ι × VectorConfig ι, G z.1 * W z.1 * (F z.2 * W z.2))
      = (∫ ξ, G ξ * W ξ) * ∫ ξ, F ξ * W ξ := by
    rw [hvol, ← integral_prod_mul (fun ξ => G ξ * W ξ) (fun ξ => F ξ * W ξ)]
  have e4 : (∫ z : VectorConfig ι × VectorConfig ι, W z.1 * (F z.2 * G z.2 * W z.2))
      = (∫ ξ, W ξ) * ∫ ξ, F ξ * G ξ * W ξ := by
    rw [hvol, ← integral_prod_mul W (fun ξ => F ξ * G ξ * W ξ)]
  have hi1 : Integrable
      (fun z : VectorConfig ι × VectorConfig ι => F z.1 * G z.1 * W z.1 * W z.2) :=
    hFGW.mul_prod hW
  have hi2 : Integrable
      (fun z : VectorConfig ι × VectorConfig ι => F z.1 * W z.1 * (G z.2 * W z.2)) :=
    hFW.mul_prod hGW
  have hi3 : Integrable
      (fun z : VectorConfig ι × VectorConfig ι => G z.1 * W z.1 * (F z.2 * W z.2)) :=
    hGW.mul_prod hFW
  have hi4 : Integrable
      (fun z : VectorConfig ι × VectorConfig ι => W z.1 * (F z.2 * G z.2 * W z.2)) :=
    hW.mul_prod hFGW
  have hf12 : Integrable (fun z : VectorConfig ι × VectorConfig ι =>
      F z.1 * G z.1 * W z.1 * W z.2 - F z.1 * W z.1 * (G z.2 * W z.2)) := hi1.sub hi2
  have hf123 : Integrable (fun z : VectorConfig ι × VectorConfig ι =>
      F z.1 * G z.1 * W z.1 * W z.2 - F z.1 * W z.1 * (G z.2 * W z.2)
        - G z.1 * W z.1 * (F z.2 * W z.2)) := hf12.sub hi3
  have hcong : (∫ z : VectorConfig ι × VectorConfig ι,
        (F z.1 - F z.2) * (G z.1 - G z.2) * W z.1 * W z.2)
      = ∫ z : VectorConfig ι × VectorConfig ι,
          (F z.1 * G z.1 * W z.1 * W z.2 - F z.1 * W z.1 * (G z.2 * W z.2)
            - G z.1 * W z.1 * (F z.2 * W z.2)) + W z.1 * (F z.2 * G z.2 * W z.2) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have hsplit : (∫ z : VectorConfig ι × VectorConfig ι,
        (F z.1 - F z.2) * (G z.1 - G z.2) * W z.1 * W z.2)
      = (∫ z : VectorConfig ι × VectorConfig ι, F z.1 * G z.1 * W z.1 * W z.2)
        - (∫ z : VectorConfig ι × VectorConfig ι, F z.1 * W z.1 * (G z.2 * W z.2))
        - (∫ z : VectorConfig ι × VectorConfig ι, G z.1 * W z.1 * (F z.2 * W z.2))
        + ∫ z : VectorConfig ι × VectorConfig ι, W z.1 * (F z.2 * G z.2 * W z.2) := by
    rw [hcong, integral_add hf123 hi4, integral_sub hf12 hi3, integral_sub hi1 hi2]
  rw [hsplit, e1, e2, e3, e4]
  ring

/-- **Doubling consequence**: if the doubled integral
`∫∫ (F(ξ)−F(ξ'))(G(ξ)−G(ξ')) W(ξ) W(ξ')` is non-negative, then
`⟨F⟩·⟨G⟩ ≤ ⟨F·G⟩` for the two-component Gibbs expectation.  This is the
truncated-pair positivity (`⟨F·G⟩ − ⟨F⟩⟨G⟩ ≥ 0`) used in (4.7.6)–(4.7.7). -/
theorem vectorExpectation_mul_le_of_doubled_nonneg (Gr : SimpleGraph ι) [Fintype Gr.edgeSet]
    {A : ℝ} (σ J h1 h2 β : ℝ) (hA : 0 < A) {F G : VectorConfig ι → ℝ}
    (hFW : Integrable (fun ξ => F ξ * vectorWeight Gr A σ J h1 h2 β ξ))
    (hGW : Integrable (fun ξ => G ξ * vectorWeight Gr A σ J h1 h2 β ξ))
    (hFGW : Integrable (fun ξ => F ξ * G ξ * vectorWeight Gr A σ J h1 h2 β ξ))
    (hnn : 0 ≤ ∫ z : VectorConfig ι × VectorConfig ι,
        (F z.1 - F z.2) * (G z.1 - G z.2)
          * vectorWeight Gr A σ J h1 h2 β z.1 * vectorWeight Gr A σ J h1 h2 β z.2) :
    vectorExpectation Gr A σ J h1 h2 β F * vectorExpectation Gr A σ J h1 h2 β G
      ≤ vectorExpectation Gr A σ J h1 h2 β (fun ξ => F ξ * G ξ) := by
  have hZ : 0 < vectorPartition Gr A σ J h1 h2 β := vectorPartition_pos Gr σ J h1 h2 β hA
  have hW : Integrable (vectorWeight Gr A σ J h1 h2 β) := integrable_vectorWeight Gr σ J h1 h2 β hA
  have hid := doubling_identity hW hFW hGW hFGW
  have hkey : (∫ ξ, F ξ * vectorWeight Gr A σ J h1 h2 β ξ)
        * (∫ ξ, G ξ * vectorWeight Gr A σ J h1 h2 β ξ)
      ≤ (∫ ξ, vectorWeight Gr A σ J h1 h2 β ξ)
        * ∫ ξ, F ξ * G ξ * vectorWeight Gr A σ J h1 h2 β ξ := by
    have hhalf : (0 : ℝ) ≤ (1 / 2) * ∫ z : VectorConfig ι × VectorConfig ι,
        (F z.1 - F z.2) * (G z.1 - G z.2)
          * vectorWeight Gr A σ J h1 h2 β z.1 * vectorWeight Gr A σ J h1 h2 β z.2 :=
      mul_nonneg (by norm_num) hnn
    linarith [hid, hhalf]
  have hZeq : (∫ ξ, vectorWeight Gr A σ J h1 h2 β ξ) = vectorPartition Gr A σ J h1 h2 β := rfl
  simp only [vectorExpectation]
  calc (vectorPartition Gr A σ J h1 h2 β)⁻¹ * (∫ ξ, F ξ * vectorWeight Gr A σ J h1 h2 β ξ)
        * ((vectorPartition Gr A σ J h1 h2 β)⁻¹
          * ∫ ξ, G ξ * vectorWeight Gr A σ J h1 h2 β ξ)
      = (vectorPartition Gr A σ J h1 h2 β)⁻¹ * (vectorPartition Gr A σ J h1 h2 β)⁻¹
          * ((∫ ξ, F ξ * vectorWeight Gr A σ J h1 h2 β ξ)
            * ∫ ξ, G ξ * vectorWeight Gr A σ J h1 h2 β ξ) := by ring
    _ ≤ (vectorPartition Gr A σ J h1 h2 β)⁻¹ * (vectorPartition Gr A σ J h1 h2 β)⁻¹
          * ((∫ ξ, vectorWeight Gr A σ J h1 h2 β ξ)
            * ∫ ξ, F ξ * G ξ * vectorWeight Gr A σ J h1 h2 β ξ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (vectorPartition Gr A σ J h1 h2 β)⁻¹
          * ∫ ξ, F ξ * G ξ * vectorWeight Gr A σ J h1 h2 β ξ := by
        rw [hZeq]; field_simp

end IsingModel.ContinuousSpin
