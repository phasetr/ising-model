import IsingModel.ContinuousSpin.TwoComponentGriffithsII
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Single-site rotated doubled moment positivity (GJ Theorem 4.7.1, scratch)

Work towards the product-form single-site moment positivity for the rotated
doubled density, the per-site engine for the second/third Griffiths inequalities.
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

/-- **One-coordinate peeling of a `Fin (n+1)`-fold Lebesgue integral.**
`∫ p, G p = ∫ x, ∫ r, G (Fin.cons x r)` via the measure-preserving head split
`(Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)`. -/
theorem integral_pi_cons {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (hG : Integrable G) :
    (∫ p : Fin (n + 1) → ℝ, G p) = ∫ x : ℝ, ∫ r : Fin n → ℝ, G (Fin.cons x r) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ)) (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hconv : (∫ p : Fin (n + 1) → ℝ, G p)
      = ∫ q : ℝ × (Fin n → ℝ),
          G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm q) :=
    (hmp.symm.integral_comp' G).symm
  rw [hconv,
    show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod (fun q : ℝ × (Fin n → ℝ) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm q))
      (hmp.symm.integrable_comp_of_integrable hG)]
  have hsymm : ∀ (x : ℝ) (r : Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x, r) = Fin.cons x r := by
    intro x r
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    rfl
  simp_rw [hsymm]

/-- The head-split symm map sends `(x, r)` to `Fin.cons x r`. -/
theorem piFinSuccAbove_symm_cons {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x, r) = Fin.cons x r := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]; rfl

/-- **A.e. integrability of the cons-substituted function.** If `G` is integrable
over `Fin (n+1) → ℝ`, then for almost every head value `x`, the tail function
`r ↦ G (Fin.cons x r)` is integrable over `Fin n → ℝ`. -/
theorem ae_integrable_cons {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (hG : Integrable G) :
    ∀ᵐ x : ℝ, Integrable (fun r : Fin n → ℝ => G (Fin.cons x r)) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ)) (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hcomp : Integrable (fun q : ℝ × (Fin n → ℝ) =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm q))
      (volume.prod volume) := hmp.symm.integrable_comp_of_integrable hG
  filter_upwards [hcomp.prod_right_ae] with x hx
  refine hx.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [piFinSuccAbove_symm_cons]

/-- **Four-fold expansion of a `Fin 4`-fold Lebesgue integral** into the iterated
form. -/
theorem integral_fin4 (F : (Fin 4 → ℝ) → ℝ) (hF : Integrable F) :
    (∫ p : Fin 4 → ℝ, F p) = ∫ a, ∫ b, ∫ c, ∫ d, F ![a, b, c, d] := by
  rw [integral_pi_cons F hF]
  refine integral_congr_ae ((ae_integrable_cons F hF).mono fun a ha => ?_)
  dsimp only
  rw [integral_pi_cons _ ha]
  refine integral_congr_ae ((ae_integrable_cons _ ha).mono fun b hb => ?_)
  dsimp only
  rw [integral_pi_cons _ hb]
  refine integral_congr_ae ((ae_integrable_cons _ hb).mono fun c hc => ?_)
  dsimp only
  rw [integral_pi_cons _ hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  dsimp only
  rw [integral_unique]
  have h1 : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
    rw [measureReal_def, volume_pi, Measure.pi_univ]; simp
  rw [h1, one_smul]
  congr 1

/-- **Product-form single-site rotated doubled moment positivity** (GJ Theorem
4.7.1 second/third inequality engine): for `A > 0`,
`0 ≤ ∫_{(Fin 4 → ℝ)} (∏ⱼ pⱼ^{eⱼ}) · rotSiteDensity A σ p`.  Reduces to the iterated
form `twoComp_single_site_nonneg` via `integral_fin4`. -/
theorem twoComp_single_site_prod_nonneg {A : ℝ} (σ : ℝ) (hA : 0 < A) (e : Fin 4 → ℕ) :
    0 ≤ ∫ p : Fin 4 → ℝ, (∏ j, p j ^ e j) * rotSiteDensity A σ p := by
  rw [integral_fin4 _ (integrable_monomial_mul_rotSiteDensity hA e)]
  simp only [rotSiteDensity, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  exact twoComp_single_site_nonneg A σ hA.le (e 0) (e 1) (e 2) (e 3)

/-- Raising the `0`- and `2`-exponents of a `Fin 4` product monomial. -/
theorem prod_pow_raise (p : Fin 4 → ℝ) (e : Fin 4 → ℕ) (m l : ℕ) :
    (∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l
      = ∏ j, p j ^ (e j + (if j = 0 then m else 0) + (if j = 2 then l else 0)) := by
  have hsplit : (∏ j, p j ^ (e j + (if j = 0 then m else 0) + (if j = 2 then l else 0)))
      = (∏ j, p j ^ e j) * (∏ j, p j ^ (if j = 0 then m else 0))
        * ∏ j, p j ^ (if j = 2 then l else 0) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [pow_add, pow_add]
  rw [hsplit]
  have h0 : (∏ j, p j ^ (if j = 0 then m else 0)) = p 0 ^ m := by
    rw [Finset.prod_eq_single 0]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have h2 : (∏ j, p j ^ (if j = 2 then l else 0)) = p 2 ^ l := by
    rw [Finset.prod_eq_single 2]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rw [h0, h2]

/-- Product-form single-site moment with extra `0`/`2`-powers, still non-negative. -/
theorem twoComp_single_site_prod_extra_nonneg {A : ℝ} (σ : ℝ) (hA : 0 < A) (e : Fin 4 → ℕ)
    (m l : ℕ) :
    0 ≤ ∫ p : Fin 4 → ℝ, (∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p := by
  have heq : ∀ p : Fin 4 → ℝ,
      (∏ j, p j ^ e j) * p 0 ^ m * p 2 ^ l * rotSiteDensity A σ p
        = (∏ j, p j ^ (e j + (if j = 0 then m else 0) + (if j = 2 then l else 0)))
            * rotSiteDensity A σ p := fun p => by rw [prod_pow_raise]
  simp_rw [heq]
  exact twoComp_single_site_prod_nonneg σ hA _

end IsingModel.ContinuousSpin
