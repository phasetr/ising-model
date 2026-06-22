import IsingModel.Dobrushin.SingleSiteGeneralComparison

/-!
# The full-volume Gibbs boundary comparison (GJ §17.1, Issue #4214 §A)

Toward the Dobrushin comparison capstone: a **support-diameter** bound on the difference of two
finite-volume Gibbs expectations under boundary conditions `η, η'` agreeing off a set `S`. The naive
"boundary-only" bound `|⟨g⟩^η_Λ − ⟨g⟩^η'_Λ| ≤ ∑_{y∈S} siteOsc y g` is **false** (boundary changes
the Gibbs weight, not just the observable); the correct bound is over the whole support diameter
`Λ ∪ S`.

* `agreesOff_union_of_agreesOff_boundary` — support configurations `σ` (for `η`) and `τ` (for `η'`)
  agree off `Λ ∪ S`.
* `gibbsExpectationBC_dist_le_sum_siteOsc_union` — `|⟨g⟩^η_Λ − ⟨g⟩^η'_Λ| ≤ ∑_{z∈Λ∪S} siteOsc z g`,
  proved from the definition: `⟨g⟩^η − ⟨g⟩^η' = (Z_η Z_η')⁻¹ ∑_σ∑_τ w_η(σ) w_η'(τ) (g σ − g τ)`,
  and weight-positive support pairs agree off `Λ ∪ S` so `|g σ − g τ| ≤ ∑_{z∈Λ∪S} siteOsc z g`.
* `gibbsExpectationBC_dist_le_volume_add_boundary_siteOsc` — the split into an interior sum over `Λ`
  and a boundary sum over `S`.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.1, pp. 304–306.
-/

namespace IsingModel

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (G : SimpleGraph ι) [Fintype G.edgeSet]

omit [Fintype ι] [Fintype G.edgeSet] in
/-- **Support configurations agree off the union** (GJ §17.1): if `σ` agrees with `η` off `Λ`, `τ`
agrees with `η'` off `Λ`, and `η` agrees with `η'` off `S`, then `σ` and `τ` agree off `Λ ∪ S`. -/
theorem agreesOff_union_of_agreesOff_boundary {Λ S : Finset ι} {η η' σ τ : Config ι}
    (hσ : agreesOff Λ η σ) (hτ : agreesOff Λ η' τ) (hη : agreesOff S η η') :
    agreesOff (Λ ∪ S) σ τ := by
  intro i hi
  rw [Finset.mem_union, not_or] at hi
  obtain ⟨hiΛ, hiS⟩ := hi
  rw [hτ i hiΛ, hη i hiS, hσ i hiΛ]

/-- **The full-volume Gibbs boundary comparison** (GJ §17.1): for boundary conditions `η, η'`
agreeing off `S`, the finite-volume Gibbs expectations differ by at most the total single-site
oscillation of `g` over the support diameter `Λ ∪ S`. Proved from the definition via the
double-sum identity `⟨g⟩^η − ⟨g⟩^η' = (Z_η Z_η')⁻¹ ∑_σ∑_τ w_η(σ) w_η'(τ) (g σ − g τ)`. -/
theorem gibbsExpectationBC_dist_le_sum_siteOsc_union
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι} (g : Config ι → ℝ)
    (hη : agreesOff S η η') :
    |gibbsExpectationBC G β J h Λ η g - gibbsExpectationBC G β J h Λ η' g|
      ≤ ∑ z ∈ Λ ∪ S, siteOsc z g := by
  classical
  set Zη := partitionFunctionBC G β J h Λ η with hZη
  set Zη' := partitionFunctionBC G β J h Λ η' with hZη'
  have hZηpos : 0 < Zη := partitionFunctionBC_pos G β J h Λ η
  have hZη'pos : 0 < Zη' := partitionFunctionBC_pos G β J h Λ η'
  set wη := boltzmannWeightBC G β J h Λ η with hwη
  set wη' := boltzmannWeightBC G β J h Λ η' with hwη'
  set D := ∑ z ∈ Λ ∪ S, siteOsc z g with hD
  have hZηne : Zη ≠ 0 := ne_of_gt hZηpos
  have hZη'ne : Zη' ≠ 0 := ne_of_gt hZη'pos
  have hwηnn : ∀ σ, 0 ≤ wη σ := fun σ => boltzmannWeightBC_nonneg G β J h Λ η σ
  have hwη'nn : ∀ τ, 0 ≤ wη' τ := fun τ => boltzmannWeightBC_nonneg G β J h Λ η' τ
  -- `Z = ∑ w` by definition.
  have hZηsum : Zη = ∑ σ, wη σ := rfl
  have hZη'sum : Zη' = ∑ τ, wη' τ := rfl
  -- the double-sum identity
  have hident : gibbsExpectationBC G β J h Λ η g - gibbsExpectationBC G β J h Λ η' g
      = (Zη * Zη')⁻¹ * ∑ σ, ∑ τ, wη σ * wη' τ * (g σ - g τ) := by
    have hexp : ∑ σ, ∑ τ, wη σ * wη' τ * (g σ - g τ)
        = (∑ σ, g σ * wη σ) * Zη' - Zη * ∑ τ, g τ * wη' τ := by
      have h1 : ∑ σ, ∑ τ, wη σ * wη' τ * g σ = (∑ σ, g σ * wη σ) * ∑ τ, wη' τ := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
      have h2 : ∑ σ, ∑ τ, wη σ * wη' τ * g τ = (∑ σ, wη σ) * ∑ τ, g τ * wη' τ := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [h1, h2, hZηsum, hZη'sum]
    rw [gibbsExpectationBC, gibbsExpectationBC, ← hZη, ← hZη', ← hwη, ← hwη', hexp]
    field_simp
  rw [hident, abs_mul]
  have hinv_nn : 0 ≤ |(Zη * Zη')⁻¹| := abs_nonneg _
  -- bound the inner double sum in absolute value
  have hsum_le : |∑ σ, ∑ τ, wη σ * wη' τ * (g σ - g τ)| ≤ D * (Zη * Zη') := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ σ, |∑ τ, wη σ * wη' τ * (g σ - g τ)| ≤ ∑ τ, wη σ * wη' τ * D := by
      intro σ
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
      by_cases hσa : agreesOff Λ η σ
      · by_cases hτa : agreesOff Λ η' τ
        · rw [abs_mul, abs_of_nonneg (mul_nonneg (hwηnn σ) (hwη'nn τ))]
          exact mul_le_mul_of_nonneg_left
            (agreesOff_dist_le_sum_siteOsc g
              (agreesOff_union_of_agreesOff_boundary hσa hτa hη))
            (mul_nonneg (hwηnn σ) (hwη'nn τ))
        · have hz : wη' τ = 0 := boltzmannWeightBC_of_not_agrees G β J h hτa
          rw [hz]; simp
      · have hz : wη σ = 0 := boltzmannWeightBC_of_not_agrees G β J h hσa
        rw [hz]; simp
    refine (Finset.sum_le_sum fun σ _ => hterm σ).trans ?_
    -- ∑_σ ∑_τ wη σ wη' τ D = D * (Zη * Zη')
    have hDsum : ∑ σ, ∑ τ, wη σ * wη' τ * D = D * (Zη * Zη') := by
      rw [hZηsum, hZη'sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hDsum]
  calc |(Zη * Zη')⁻¹| * |∑ σ, ∑ τ, wη σ * wη' τ * (g σ - g τ)|
      ≤ |(Zη * Zη')⁻¹| * (D * (Zη * Zη')) :=
        mul_le_mul_of_nonneg_left hsum_le hinv_nn
    _ = D := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Zη * Zη')⁻¹)]
        field_simp

/-- **Interior/boundary split of the Gibbs boundary comparison** (GJ §17.1): the comparison is
bounded by an interior sum over `Λ` plus a boundary sum over the differing set `S`. -/
theorem gibbsExpectationBC_dist_le_volume_add_boundary_siteOsc
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ S : Finset ι) {η η' : Config ι} (g : Config ι → ℝ)
    (hη : agreesOff S η η') :
    |gibbsExpectationBC G β J h Λ η g - gibbsExpectationBC G β J h Λ η' g|
      ≤ (∑ x ∈ Λ, siteOsc x g) + ∑ y ∈ S, siteOsc y g := by
  refine (gibbsExpectationBC_dist_le_sum_siteOsc_union G β J h Λ S g hη).trans ?_
  have hle : ∑ z ∈ Λ ∪ S, siteOsc z g
      ≤ (∑ z ∈ Λ, siteOsc z g) + ∑ z ∈ S, siteOsc z g := by
    rw [← Finset.sum_union_inter]
    have : 0 ≤ ∑ z ∈ Λ ∩ S, siteOsc z g :=
      Finset.sum_nonneg fun z _ => siteOsc_nonneg z g
    linarith
  exact hle

end Dobrushin

end IsingModel
