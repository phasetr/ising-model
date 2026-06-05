import IsingModel.Inequalities.GKSBoundaryConditionII
import IsingModel.InfiniteVolume.Boundedness

/-!
# Coupling monotonicity of the `+` boundary-condition state (FV §3.6, Issue #3605)

The `+` boundary correlation `⟨σ^B⟩⁺_Λ` is monotone increasing in the uniform
coupling `J` (the boundary analogue of `correlation_monotone_J`, Glimm–Jaffe
Prop. 4.2.1).  The proof mirrors the free-state route: the reweighting factor
`R(σ) = exp(β(J₂−J₁)·Σ edgeSpin)` has non-negative correlations, and the resulting
`+`-state covariance bound follows from the Walsh/Fourier expansion of `R` together
with the boundary GKS-II inequality `gibbsExpectationBC_plus_gks_second` (#3607).

* `cov_hnc_boltzmannBC_nonneg` — the `+`-state covariance bound for an HNC factor.
* `gibbsExpectationBC_plus_reweighting_nonneg` — the `J`-reweighting inequality.
* `gibbsExpectationBC_plus_monotone_J` — `⟨σ^B⟩⁺_Λ` nondecreasing in `J`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6; Glimm–Jaffe Prop. 4.2.1.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`+`-state covariance bound for an HNC factor**: for a function `f` with
non-negative correlations, the `+`-boundary covariance of `σ^B` with `f` is
non-negative.  The boundary analogue of `cov_hnc_boltzmann_nonneg`, proved by the
Walsh/Fourier expansion of `f` and the boundary GKS-II inequality. -/
theorem cov_hnc_boltzmannBC_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J h : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι)
    (f : Config ι → ℝ) (hf : HasNonnegCorrelations f) (B : Finset ι) :
    0 ≤ (∑ σ, spinProduct B σ * f σ *
            boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
          (∑ σ, boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) -
        (∑ σ, spinProduct B σ *
            boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
          (∑ σ, f σ * boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) := by
  let ĉ : Finset ι → ℝ := fun S =>
    (Fintype.card (Config ι) : ℝ)⁻¹ * ∑ τ, spinProduct S τ * f τ
  have hĉ_nonneg : ∀ S, 0 ≤ ĉ S := fun S =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hf S)
  have hfourier : ∀ σ, f σ = ∑ S : Finset ι, ĉ S * spinProduct S σ :=
    walsh_fourier_inversion f
  have hprod : ∀ σ, spinProduct B σ * f σ =
      ∑ S, ĉ S * spinProduct (symmDiff B S) σ := by
    intro σ; rw [hfourier σ, Finset.mul_sum]
    congr 1; ext S; rw [← spinProduct_mul]; ring
  have hterm : ∀ S : Finset ι,
      0 ≤ ĉ S * ((∑ σ, spinProduct (symmDiff B S) σ *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
        (∑ σ, boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) -
        (∑ σ, spinProduct B σ *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
        (∑ σ, spinProduct S σ *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ)) := by
    intro S; apply mul_nonneg (hĉ_nonneg S)
    have hZ := partitionFunctionBC_pos G β (fun _ => J) h Λ (plusConfig ι)
    have hgks := gibbsExpectationBC_plus_gks_second G hβ hJ hh Λ B S
    unfold gibbsExpectationBC at hgks
    have h1 := mul_le_mul_of_nonneg_left hgks hZ.le
    have h2 := mul_le_mul_of_nonneg_right h1 hZ.le
    unfold partitionFunctionBC at h2
    field_simp [ne_of_gt hZ] at h2
    have h3 := (div_le_iff₀ hZ).mp h2
    unfold partitionFunctionBC at h3
    have h3a : (∑ σ : Config ι, boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
        ((∑ x, spinProduct B x * boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) x) *
          (∑ x, spinProduct S x * boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) x)) ≤
        (∑ σ : Config ι, boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ) *
        ((∑ x, spinProduct (symmDiff B S) x *
            boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) x) *
          (∑ σ : Config ι, boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ)) := by
      nlinarith
    linarith [le_of_mul_le_mul_left h3a hZ]
  have eq2 : ∑ σ : Config ι, f σ * boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ =
      ∑ S : Finset ι, ĉ S * ∑ σ : Config ι,
        spinProduct S σ * boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ := by
    simp_rw [hfourier, Finset.sum_mul]
    exact (Finset.sum_comm).trans (Finset.sum_congr rfl (fun S _ => by
      simp_rw [show ∀ x, ĉ S * spinProduct S x *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) x =
        ĉ S * (spinProduct S x *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) x) from fun _ => by ring]
      rw [← Finset.mul_sum]))
  have hnum1 : ∑ σ : Config ι,
      (∑ S : Finset ι, ĉ S * spinProduct (symmDiff B S) σ) *
      boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ =
      ∑ S : Finset ι, ĉ S * ∑ σ : Config ι,
        spinProduct (symmDiff B S) σ *
          boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    congr 1; ext S; simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  simp_rw [hprod]
  rw [hnum1, eq2]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_nonneg (fun S _ => by convert hterm S using 1; ring)

omit [DecidableEq ι] in
/-- **The `J`-reweighting identity for the `+` boundary weight**:
`w⁺_{J₂}(σ) = R(σ)·w⁺_{J₁}(σ)` where `R(σ) = exp(β(J₂−J₁)·Σ edgeSpin)`. -/
theorem boltzmannWeightBC_plus_reweight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J₁ J₂ h : ℝ) (Λ : Finset ι) (σ : Config ι) :
    boltzmannWeightBC G β (fun _ => J₂) h Λ (plusConfig ι) σ
      = (∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) *
          boltzmannWeightBC G β (fun _ => J₁) h Λ (plusConfig ι) σ := by
  have hbw : boltzmannWeightJ G β (fun _ => J₂) h σ =
      (∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) *
        boltzmannWeightJ G β (fun _ => J₁) h σ := by
    rw [boltzmannWeightJ_uniform_eq, boltzmannWeightJ_uniform_eq]
    unfold boltzmannWeight
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [← Finset.mul_sum]; ring
  unfold boltzmannWeightBC
  by_cases hag : agreesOff Λ (plusConfig ι) σ
  · rw [Set.indicator_of_mem hag, Set.indicator_of_mem hag, hbw]
  · rw [Set.indicator_of_notMem hag, Set.indicator_of_notMem hag, mul_zero]

/-- **`J`-reweighting inequality for the `+` boundary state**: for `0 ≤ J₁ ≤ J₂`,
`num⁺_{J₂}(B)·Z⁺_{J₁} − num⁺_{J₁}(B)·Z⁺_{J₂} ≥ 0`. -/
theorem gibbsExpectationBC_plus_reweighting_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (Λ : Finset ι) (B : Finset ι) (J₁ J₂ : ℝ) (hJ : J₁ ≤ J₂)
    (hJ₁ : 0 ≤ J₁) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 ≤ (∑ σ, spinProduct B σ *
            boltzmannWeightBC G β (fun _ => J₂) h Λ (plusConfig ι) σ) *
          (∑ σ, boltzmannWeightBC G β (fun _ => J₁) h Λ (plusConfig ι) σ) -
        (∑ σ, spinProduct B σ *
            boltzmannWeightBC G β (fun _ => J₁) h Λ (plusConfig ι) σ) *
          (∑ σ, boltzmannWeightBC G β (fun _ => J₂) h Λ (plusConfig ι) σ) := by
  have hR : HasNonnegCorrelations (fun σ =>
      ∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => β * (J₂ - J₁)) (fun _ => 0)
      (fun _ _ => mul_nonneg hβ.le (sub_nonneg.mpr hJ))
      (fun _ => le_refl 0) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, mul_one] at hhnc
    exact hhnc
  simp_rw [boltzmannWeightBC_plus_reweight G β J₁ J₂ h Λ]
  simp only [← mul_assoc]
  exact cov_hnc_boltzmannBC_nonneg G hβ hJ₁ hh Λ _ hR B

/-- **Coupling monotonicity of the `+` boundary correlation** (Glimm–Jaffe Prop. 4.2.1,
boundary analogue): `⟨σ^B⟩⁺_Λ` is monotone increasing in the uniform coupling `J` on
`[0,∞)`. -/
theorem gibbsExpectationBC_plus_monotone_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (Λ : Finset ι) (B : Finset ι) :
    MonotoneOn (fun J => gibbsExpectationBC G β (fun _ => J) h Λ (plusConfig ι)
      (spinProduct B)) (Set.Ici 0) := by
  have hden_pos : ∀ J : ℝ, 0 < ∑ σ : Config ι,
      boltzmannWeightBC G β (fun _ => J) h Λ (plusConfig ι) σ := fun J =>
    partitionFunctionBC_pos G β (fun _ => J) h Λ (plusConfig ι)
  intro J₁ hJ₁_mem J₂ _hJ₂_mem hJ
  simp only [gibbsExpectationBC]
  unfold partitionFunctionBC
  rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ (hden_pos J₁) (hden_pos J₂)]
  exact le_of_sub_nonneg (gibbsExpectationBC_plus_reweighting_nonneg G h β Λ B J₁ J₂ hJ
    (Set.mem_Ici.mp hJ₁_mem) hh hβ)

end IsingModel
