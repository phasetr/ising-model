import IsingModel.InfiniteVolume
import IsingModel.LeeYang
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Free energy and analyticity

The free energy of the finite-volume Ising model, and its analyticity
from the Lee-Yang theorem.

## Main results

* `freeEnergy` — free energy per site: `f = |ι|⁻¹ ln Z`
* `partitionFunction_monotone_h` — `Z` is monotone increasing in `h` on `[0,∞)`
* `freeEnergy_monotone_h` — `f` is monotone increasing in `h` on `[0,∞)`

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6, pp. 67–70.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and Triviality
  in Quantum Field Theory*, Chapter 11.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Free energy definition (equation 4.6.1) -/

/-- **Free energy per site** (Glimm–Jaffe, (4.6.1), p. 67):
`f = |ι|⁻¹ · ln Z`. Well-defined since `Z > 0` (`partitionFunction_pos`). -/
noncomputable def freeEnergy (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G p)

/-- The free energy as a function of the coupling constant `J`,
with `h` and `β` fixed. -/
noncomputable def freeEnergyJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) : ℝ → ℝ :=
  fun J => freeEnergy G ⟨J, h, β⟩

/-- The free energy as a function of the external field `h`,
with `J` and `β` fixed. -/
noncomputable def freeEnergyH (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) : ℝ → ℝ :=
  fun h => freeEnergy G ⟨J, h, β⟩

/-! ## Partition function monotonicity in h

For ferromagnetic parameters (`J ≥ 0`, `β > 0`), the partition function
is monotone increasing in the external field `h` on `[0, ∞)`.

The proof uses reweighting: for `h₁ ≤ h₂`,
`Z(h₂) = Z(h₁) · ⟨R⟩₁` where `R(σ) = exp(β(h₂-h₁) Σ sign(σ_i))`.
The Fourier coefficient `ĉ_∅ = cosh(β(h₂-h₁))^|ι| ≥ 1` since
`R` factors over independent sites, and all other terms
`ĉ_S ⟨σ^S⟩ ≥ 0` by HNC of `R` and GKS-I.

Reference: Glimm–Jaffe, §4.6, p. 67 (implicit in the analyticity proof). -/

/-- The reweighting identity for the partition function in `h`:
`Z(h₂) = Σ_σ R(σ) · w₁(σ)` where `R = exp(β(h₂-h₁) Σ sign(σ_i))`.
This expresses `exp(-β H_{h₂}) = R · exp(-β H_{h₁})`. -/
private theorem partitionFunction_reweight_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₁ h₂ : ℝ) :
    partitionFunction G ⟨J, h₂, β⟩ =
    ∑ σ : Config ι,
      (∏ i : ι, Real.exp (β * (h₂ - h₁) * Spin.sign ℝ (σ i))) *
      boltzmannWeight G ⟨J, h₁, β⟩ σ := by
  unfold partitionFunction boltzmannWeight
  congr 1; ext σ
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  unfold hamiltonian interactionEnergy externalFieldEnergy
  simp only [← Finset.mul_sum]; ring

/-- The partition function is monotone increasing in `h` on `[0, ∞)`.

For `0 ≤ h₁ ≤ h₂`, `J ≥ 0`, `β > 0`:
`Z(J, h₂, β) ≥ Z(J, h₁, β)`.

Proof: `Z(h₂) = ⟨R⟩_{h₁} · Z(h₁)` where `R = ∏ exp(β(h₂-h₁) sign)`.
`R` has HNC, and `⟨R⟩ = Σ ĉ_S ⟨σ^S⟩ ≥ ĉ_∅ ≥ cosh(β(h₂-h₁))^|ι| ≥ 1`
by Walsh–Fourier expansion and GKS-I. -/
theorem partitionFunction_monotone_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (h₁ h₂ : ℝ)
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    partitionFunction G ⟨J, h₁, β⟩ ≤ partitionFunction G ⟨J, h₂, β⟩ := by
  -- R(σ) = ∏ exp(β(h₂-h₁) sign(σ_i)), the reweighting factor
  let K := β * (h₂ - h₁)
  -- R has HNC by hasNonnegCorrelations_edge_site_product
  have hR : HasNonnegCorrelations (fun σ : Config ι =>
      ∏ i : ι, Real.exp (K * Spin.sign ℝ (σ i))) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => 0) (fun _ => K)
      (fun _ _ => le_refl 0)
      (fun _ => mul_nonneg hβ.le (sub_nonneg.mpr hh)) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, one_mul] at hhnc
    exact hhnc
  -- p₁ = ⟨J, h₁, β⟩ is ferromagnetic
  have hferm : Ferromagnetic (⟨J, h₁, β⟩ : IsingParams ℝ) := ⟨hJ, hh₁, hβ⟩
  -- Use cov_hnc_boltzmann_nonneg with B = ∅ to get the covariance bound
  -- Actually we use a direct argument: Z(h₂) = Σ R w₁ and show Σ R w₁ ≥ Σ w₁
  -- by Fourier expanding R = Σ ĉ_S σ^S and using ĉ_S ≥ 0, ⟨σ^S⟩ ≥ 0
  rw [partitionFunction_reweight_h G J β h₁ h₂]
  -- Goal: Z₁ ≤ Σ R w₁ where R(σ) = ∏ exp(K sign(σ_i))
  -- Strategy: exp(x) ≥ 1 + x, so R(σ) ≥ 1 + K Σ sign(σ_i)
  -- Then Σ R w₁ ≥ Σ (1 + K Σ sign) w₁ = Z₁ + K Σᵢ numᵢ ≥ Z₁ (by GKS-I)
  -- Step 1: R(σ) = exp(K Σ sign) (product → sum in exponent)
  have hRexp : ∀ σ : Config ι, (∏ i : ι, Real.exp (K * Spin.sign ℝ (σ i))) =
      Real.exp (∑ i : ι, K * Spin.sign ℝ (σ i)) := fun σ => by
    rw [← Real.exp_sum]
  -- Step 2: exp(x) ≥ 1 + x for all x
  have hexp_lb : ∀ σ : Config ι,
      1 + K * ∑ i : ι, Spin.sign ℝ (σ i) ≤
        (∏ i : ι, Real.exp (K * Spin.sign ℝ (σ i))) := by
    intro σ; rw [hRexp, ← Finset.mul_sum]
    linarith [Real.add_one_le_exp (K * ∑ i : ι, Spin.sign ℝ (σ i))]
  -- Step 3: Σ R w₁ ≥ Σ (1 + K Σ sign) w₁
  have hsum_lb : ∑ σ : Config ι, (1 + K * ∑ i, Spin.sign ℝ (σ i)) *
      boltzmannWeight G ⟨J, h₁, β⟩ σ ≤
    ∑ σ : Config ι, (∏ i : ι, Real.exp (K * Spin.sign ℝ (σ i))) *
      boltzmannWeight G ⟨J, h₁, β⟩ σ := by
    apply Finset.sum_le_sum; intro σ _
    exact mul_le_mul_of_nonneg_right (hexp_lb σ) (boltzmannWeight_pos G _ σ).le
  -- Step 4: Σ (1 + K Σ sign) w₁ = Z₁ + K Σᵢ numᵢ
  have hexpand : ∑ σ : Config ι, (1 + K * ∑ i, Spin.sign ℝ (σ i)) *
      boltzmannWeight G ⟨J, h₁, β⟩ σ =
    partitionFunction G ⟨J, h₁, β⟩ +
    K * ∑ i : ι, ∑ σ : Config ι, Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, h₁, β⟩ σ := by
    unfold partitionFunction
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro σ _; ring
  -- Step 5: Each numᵢ = Σ σ_i w₁ ≥ 0 by GKS-I (⟨σ_i⟩ ≥ 0)
  have hnum_nonneg : ∀ i : ι,
      0 ≤ ∑ σ : Config ι, Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, h₁, β⟩ σ := by
    intro i
    -- Spin.sign(σ_i) = spinProduct {i} σ
    have hspin : ∀ σ : Config ι, Spin.sign ℝ (σ i) = spinProduct {i} σ := by
      intro σ; unfold spinProduct Spin.sign; simp
    simp_rw [hspin]
    exact (boltzmannWeight_hasNonnegCorrelations G ⟨J, h₁, β⟩ hferm) {i}
  -- Step 6: Combine: Z₁ + K · (non-negative) ≥ Z₁
  calc partitionFunction G ⟨J, h₁, β⟩
      ≤ partitionFunction G ⟨J, h₁, β⟩ +
        K * ∑ i : ι, ∑ σ : Config ι,
          Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, h₁, β⟩ σ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hh))
          (Finset.sum_nonneg (fun i _ => hnum_nonneg i)))
    _ = ∑ σ : Config ι, (1 + K * ∑ i, Spin.sign ℝ (σ i)) *
        boltzmannWeight G ⟨J, h₁, β⟩ σ := hexpand.symm
    _ ≤ _ := hsum_lb

/-! ## Free energy monotonicity

From `partitionFunction_monotone_h` and the monotonicity of `Real.log`. -/

/-- The free energy is monotone increasing in `h` on `[0, ∞)`.
Since `Z(h₂) ≥ Z(h₁) > 0`, we have `ln Z(h₂) ≥ ln Z(h₁)`,
hence `f(h₂) ≥ f(h₁)`. -/
theorem freeEnergy_monotone_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    MonotoneOn (freeEnergyH G J β) (Set.Ici 0) := by
  intro h₁ hh₁ h₂ _ hh
  unfold freeEnergyH freeEnergy
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Real.log_le_log (partitionFunction_pos G ⟨J, h₁, β⟩)
    (partitionFunction_monotone_h G J β hJ hβ h₁ h₂ (Set.mem_Ici.mp hh₁) hh)

/-! ## Analyticity of the partition polynomial (Theorem 4.6.2, finite volume)

The Lee-Yang circle theorem (`lee_yang_circle`) shows that the Ising
partition polynomial `P(z) = Σ_{X⊆ι} w(X) ∏_{i∈X} z_i` does not vanish
on the open unit polydisk `{z : |z_k| < 1}`.

Since `P` is a polynomial (hence entire/analytic), and `log` is analytic
on the slit plane `{w : Re w > 0 ∨ Im w ≠ 0}`, the composition
`log ∘ P` is analytic wherever `P(z) ∈ slitPlane`.

The connection between the polynomial `isingEdgePoly` (in `LeeYang.lean`)
and the Boltzmann partition function `partitionFunction` (in `GibbsMeasure.lean`)
uses `z_i = e^{-2βh_i}`, `t_e = e^{-2βJ_e}` (Friedli–Velenik, (3.63)–(3.65)).

For the full formalization of the analyticity domain, we need to show
that `isingEdgePoly.eval z ∈ Complex.slitPlane` (not just `≠ 0`) on the
open unit polydisk. This follows from the continuity of the polynomial
and the fact that `P(0) > 0` (the constant term is positive), but the
argument requires tracking the winding number. This is deferred to
future work.

Reference: Glimm–Jaffe, Theorem 4.6.2, p. 68. -/

end IsingModel
