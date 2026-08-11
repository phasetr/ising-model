import IsingModel.InfiniteVolume.MonotoneJ

/-!
# Infinite-volume correlations split — monotonicity in external field and correlation bounds

Part of the split infinite-volume correlation layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in external field (Proposition 4.2.1 at the singleton couplings)

The correlation function `⟨σ^B⟩` is monotone increasing in the external
field `h`. This follows from GKS-II via the reweighting factor
`R(σ) = ∏_i exp(β(h₂-h₁) · sign(σ_i))`, which has HNC.

Reference: Glimm–Jaffe, Proposition 4.2.1, p. 58 (correlations are monotone
increasing in the couplings `J_A`), applied to the singleton couplings that
carry `h`; the same page remarks that the Ising measure stays ferromagnetic
for `0 ≤ h`. -/

/-- The correlation function as a function of h (external field),
with J and β fixed. -/
noncomputable def correlationH (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (B : Finset ι) : ℝ → ℝ :=
  fun h => correlation G ⟨J, h, β⟩ B

/-- The reweighting inequality for correlation functions in h.
For `0 ≤ h₁ ≤ h₂`, the numerator cross-difference is non-negative. -/
private theorem correlation_reweighting_h_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (B : Finset ι) (h₁ h₂ : ℝ) (hh : h₁ ≤ h₂)
    (hJ : 0 ≤ J) (hh₁ : 0 ≤ h₁) (hβ : 0 < β) :
    0 ≤ (∑ σ : Config ι, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J, h₂, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J, h₁, β⟩ σ)) -
      (∑ σ, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J, h₁, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J, h₂, β⟩ σ)) := by
  -- Step 1: Hamiltonian splitting: exp(-β H_{h₂}) = R · exp(-β H_{h₁})
  -- where R(σ) = ∏_i exp(β(h₂-h₁) · sign(σ_i))
  have hexp : ∀ σ, Real.exp (-β * hamiltonian G ⟨J, h₂, β⟩ σ) =
      (∏ i : ι, Real.exp (β * (h₂ - h₁) * Spin.sign ℝ (σ i))) *
      Real.exp (-β * hamiltonian G ⟨J, h₁, β⟩ σ) := by
    intro σ
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [Spin.sign, ← Finset.mul_sum]; ring
  -- Step 2: R has non-negative correlations (HNC)
  have hR : HasNonnegCorrelations (fun σ =>
      ∏ i : ι, Real.exp (β * (h₂ - h₁) * Spin.sign ℝ (σ i))) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => 0) (fun _ => β * (h₂ - h₁))
      (fun _ _ => le_refl 0)
      (fun _ => mul_nonneg hβ.le (sub_nonneg.mpr hh)) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, one_mul] at hhnc
    convert hhnc using 1
  -- Step 3: ⟨J, h₁, β⟩ is ferromagnetic
  have hferm : Ferromagnetic (⟨J, h₁, β⟩ : IsingParams ℝ) := ⟨hJ, hh₁, hβ⟩
  -- Step 4: Apply cov_hnc_boltzmann_nonneg
  simp_rw [hexp]
  simp only [← mul_assoc]
  exact cov_hnc_boltzmann_nonneg G ⟨J, h₁, β⟩ hferm _ hR B

/-- **h-monotonicity** (Glimm–Jaffe, Proposition 4.2.1, p. 58, applied to the
singleton couplings): the correlation function is monotone increasing in h
on `[0, ∞)`.

Proof: For `0 ≤ h₁ ≤ h₂`, use the reweighting factor
`R = ∏_i exp(β(h₂-h₁) · sign(σ_i))` (which has HNC) and `gks_second`. -/
theorem correlation_monotone_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    MonotoneOn (correlationH G J β B) (Set.Ici 0) := by
  let E : ℝ → Config ι → ℝ := fun h σ =>
    -β * hamiltonian G ⟨J, h, β⟩ σ
  let den : ℝ → ℝ := fun h => ∑ σ : Config ι, Real.exp (E h σ)
  have hden_pos : ∀ h, 0 < den h := fun h =>
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  let num : ℝ → ℝ := fun h =>
    ∑ σ : Config ι, spinProduct B σ * Real.exp (E h σ)
  have hf_eq : correlationH G J β B = num / den := by
    ext h; simp only [correlationH, correlation, gibbsExpectation,
      partitionFunction, boltzmannWeight, Pi.div_apply, div_eq_mul_inv]
    ring
  intro h₁ hh₁_mem h₂ _hh₂_mem hh
  simp only [hf_eq, Pi.div_apply]
  rw [div_le_div_iff₀ (hden_pos h₁) (hden_pos h₂)]
  exact le_of_sub_nonneg (correlation_reweighting_h_nonneg G J β B h₁ h₂ hh
    hJ (Set.mem_Ici.mp hh₁_mem) hβ)

/-! ## Upper bound on the correlation (without absolute value) -/

/-- The correlation function is bounded above by `1`.
Extracted from `abs_correlation_le_one` via `a ≤ |a|`. -/
theorem correlation_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A ≤ 1 :=
  le_trans (le_abs_self _) (abs_correlation_le_one G p A)

/-- The correlation function is bounded below by `-1`.
Extracted from `abs_correlation_le_one` via the `abs_le` characterization. -/
theorem neg_one_le_correlation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    -1 ≤ correlation G p A :=
  (abs_le.mp (abs_correlation_le_one G p A)).1

/-- **`correlation² ≤ 1`** unconditionally. From `abs_correlation_le_one`
via `pow_le_pow_left₀` + `sq_abs`. -/
theorem correlation_sq_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A ^ 2 ≤ 1 := by
  have h := abs_correlation_le_one G p A
  have : |correlation G p A| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this


end IsingModel
