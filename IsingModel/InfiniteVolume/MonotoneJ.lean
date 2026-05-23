import IsingModel.InfiniteVolume.Boundedness

/-!
# Infinite-volume correlations split — monotonicity in J and convergence of correlations

Part of the split infinite-volume correlation layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in coupling constant (Proposition 4.2.1)

The correlation function `⟨σ^B⟩` is monotone increasing in the coupling
constant `J`. This follows from GKS-II:
`∂⟨σ^B⟩/∂J_A = ⟨σ^A σ^B⟩ - ⟨σ^A⟩⟨σ^B⟩ ≥ 0`.

In the discrete setting, we show that for `J₁ ≤ J₂` (with all other
parameters fixed), `⟨σ^B⟩_{J₁} ≤ ⟨σ^B⟩_{J₂}`.

The proof uses the reweighting factor `R(σ) = ∏ exp(β(J₂-J₁) edgeSpin)`,
which has HNC. The Hamiltonian splitting `exp(-β H_{J₂}) = R · exp(-β H_{J₁})`
reduces to a covariance bound via `cov_hnc_boltzmann_nonneg`.

Reference: Glimm–Jaffe, Proposition 4.2.1, p. 58. -/

/-- The correlation function as a function of J (coupling constant),
with h and β fixed. -/
noncomputable def correlationJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) : ℝ → ℝ :=
  fun J => correlation G ⟨J, h, β⟩ B

/-- The reweighting inequality for correlation functions.
For `0 ≤ J₁ ≤ J₂`, `num J₂ * den J₁ - num J₁ * den J₂ ≥ 0`.

Proof: `exp(E J₂ σ) = R(σ) · exp(E J₁ σ)` where
`R(σ) = exp(β(J₂-J₁) Σ edgeSpin)`. Fourier expand R = Σ_S ĉ_S σ^S
(ĉ_S ≥ 0 by HNC of R). Then the difference equals
`Σ_S ĉ_S · Z₁² (corr₁(B△S) - corr₁(B)·corr₁(S)) ≥ 0`
by `gks_second` for each term. -/
private theorem correlation_reweighting_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) (J₁ J₂ : ℝ) (hJ : J₁ ≤ J₂)
    (hJ₁ : 0 ≤ J₁) (hh : 0 ≤ h) (hβ : 0 < β) :
    0 ≤ (∑ σ : Config ι, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J₂, h, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J₁, h, β⟩ σ)) -
      (∑ σ, spinProduct B σ * Real.exp
          (-β * hamiltonian G ⟨J₁, h, β⟩ σ)) *
        (∑ σ, Real.exp (-β * hamiltonian G ⟨J₂, h, β⟩ σ)) := by
  -- exp(E J₂ σ) = exp(E J₁ σ) · R(σ) where R = exp(β(J₂-J₁) Σ edgeSpin)
  -- Fourier expand R = Σ_S ĉ_S σ^S (ĉ_S ≥ 0 by HNC)
  -- LHS = Σ_S ĉ_S · Z₁² · (corr₁(B△S) - corr₁(B)·corr₁(S)) ≥ 0
  -- Each factor: ĉ_S ≥ 0, Z₁² ≥ 0, corr₁(B△S) - corr₁(B)·corr₁(S) ≥ 0 by gks_second.
  -- Step 1: Hamiltonian splitting: exp(-β H_{J₂}) = R · exp(-β H_{J₁})
  -- where R(σ) = ∏_e exp(β(J₂-J₁) edgeSpin(σ,e))
  have hexp : ∀ σ, Real.exp (-β * hamiltonian G ⟨J₂, h, β⟩ σ) =
      (∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) *
      Real.exp (-β * hamiltonian G ⟨J₁, h, β⟩ σ) := by
    intro σ
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [← Finset.mul_sum]; ring
  -- Step 2: R has non-negative correlations (HNC)
  -- by hasNonnegCorrelations_edge_site_product with edgeK = β(J₂-J₁), siteK = 0
  have hR : HasNonnegCorrelations (fun σ =>
      ∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) := by
    intro S
    have hhnc := hasNonnegCorrelations_edge_site_product G
      (fun _ => β * (J₂ - J₁)) (fun _ => 0)
      (fun _ _ => mul_nonneg hβ.le (sub_nonneg.mpr hJ))
      (fun _ => le_refl 0) S
    simp only [zero_mul, Real.exp_zero, Finset.prod_const_one, mul_one] at hhnc
    exact hhnc
  -- Step 3: ⟨J₁, h, β⟩ is ferromagnetic
  have hferm : Ferromagnetic (⟨J₁, h, β⟩ : IsingParams ℝ) := ⟨hJ₁, hh, hβ⟩
  -- Step 4: Rewrite exp(-β H_{J₂}) → R · exp(-β H_{J₁}) and apply cov_hnc_boltzmann_nonneg
  simp_rw [hexp]
  -- Goal: 0 ≤ (Σ σ^B · (R · w₁))(Σ w₁) - (Σ σ^B · w₁)(Σ R · w₁)
  -- Reassociate multiplication and unfold boltzmannWeight
  simp only [← mul_assoc]
  exact cov_hnc_boltzmann_nonneg G ⟨J₁, h, β⟩ hferm _ hR B

/-- **Proposition 4.2.1** (Glimm–Jaffe, p. 58):
The correlation function is monotone increasing in J on `[0, ∞)`.

Proof: For `0 ≤ J₁ ≤ J₂`, use Fourier expansion of the reweighting factor
`R = exp(β(J₂-J₁) Σ edgeSpin)` and `gks_second` for each Fourier term. -/
theorem correlation_monotone_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    MonotoneOn (correlationJ G h β B) (Set.Ici 0) := by
  -- f(J) = num(J) / den(J) where
  -- num(J) = Σ_σ spinProduct B σ * exp(-β * H_J(σ))
  -- den(J) = Σ_σ exp(-β * H_J(σ)) = partitionFunction
  -- H_J(σ) = -J * Σ edgeSpin - h * Σ sign
  -- So exp(-β H_J) = exp(βJ Σ edgeSpin + βh Σ sign)
  -- Both num and den are finite sums of exp(affine in J), hence differentiable.
  -- deriv f = (num' den - num den') / den²
  -- = β/den² Σ_σ Σ_τ σ^B (S(σ) - S(τ)) w(σ) w(τ)
  -- = β/den² Σ_e duplicateSum(B, e) ≥ 0
  -- by duplicateSum_nonneg.
  -- Hence Monotone by monotone_of_deriv_nonneg.
  -- Define the exponent as a function of J and σ
  let E : ℝ → Config ι → ℝ := fun J σ =>
    -β * hamiltonian G ⟨J, h, β⟩ σ
  -- den(J) = Σ exp(E J σ), positive
  let den : ℝ → ℝ := fun J => ∑ σ : Config ι, Real.exp (E J σ)
  have hden_pos : ∀ J, 0 < den J := fun J =>
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hden_ne : ∀ J, den J ≠ 0 := fun J => ne_of_gt (hden_pos J)
  -- num(J) = Σ σ^B exp(E J σ) is differentiable
  let num : ℝ → ℝ := fun J =>
    ∑ σ : Config ι, spinProduct B σ * Real.exp (E J σ)
  -- f = num / den is differentiable
  have hf_eq : correlationJ G h β B = num / den := by
    ext J; simp only [correlationJ, correlation, gibbsExpectation,
      partitionFunction, boltzmannWeight, Pi.div_apply, div_eq_mul_inv]
    ring
  -- Direct algebraic proof: for J₁ ≤ J₂, show corr(J₂) ≥ corr(J₁)
  -- by rewriting corr(J₂) - corr(J₁) = [num₂ den₁ - num₁ den₂] / (den₁ den₂)
  -- and showing the numerator ≥ 0 using GKS-II.
  intro J₁ hJ₁_mem J₂ _hJ₂_mem hJ
  simp only [hf_eq, Pi.div_apply]
  rw [div_le_div_iff₀ (hden_pos J₁) (hden_pos J₂)]
  -- Goal: num J₁ * den J₂ ≤ num J₂ * den J₁
  -- Use the reweighting R(σ) = exp(β(J₂-J₁) Σ edgeSpin) which has HNC,
  -- and the Walsh/Fourier expansion R = Σ_S ĉ_S σ^S (ĉ_S ≥ 0 by HNC).
  -- Then num J₂ * den J₁ - num J₁ * den J₂
  --   = Σ_S ĉ_S · duplicateSum(⟨J₁,h,β⟩, B, S) ≥ 0
  -- by duplicateSum_nonneg.
  -- Walsh orthogonality (walsh_orthogonality, walsh_normalization) proved.
  -- The Fourier inversion identity and the algebraic connection
  -- to duplicateSum are the remaining formalization work.
  -- Apply hnc_correlation_nonneg via reweighting identity:
  -- exp(E J₂ σ) = R(σ) · exp(E J₁ σ) where R(σ) = exp(β(J₂-J₁) Σ edgeSpin)
  -- R has HNC → cov_hnc_boltzmann_nonneg gives the bound.
  exact le_of_sub_nonneg (correlation_reweighting_nonneg G h β B J₁ J₂ hJ
    (Set.mem_Ici.mp hJ₁_mem) hh hβ)

/-! ## Convergence of correlation functions (Theorem 4.2.3)

For the ferromagnetic Ising model with h ≥ 0, the correlation function
`⟨σ^B⟩` converges as the coupling constant J → ∞. The proof combines:
- Monotonicity: `⟨σ^B⟩` increases with J (Proposition 4.2.1)
- Boundedness: `|⟨σ^B⟩| ≤ 1` (Proposition 4.2.2)
- Monotone bounded sequences converge (`tendsto_atTop_ciSup`)

In the finite lattice setting, "Λ grows" means coupling constants increase
from 0 to their full values, and the correlation function is a monotone
bounded function of J.

Reference: Glimm–Jaffe, Theorem 4.2.3, p. 59. -/

/-- The correlation function is non-negative for ferromagnetic parameters.
For `J ≥ 0`, `h ≥ 0`, `β > 0`: `⟨σ^B⟩ ≥ 0` by GKS-I. -/
theorem correlationJ_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι)
    (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ correlationJ G h β B J :=
  gks_first G ⟨J, h, β⟩ ⟨hJ, hh, hβ⟩ B

/-- The correlation function is bounded above by 1.
From `|⟨σ^B⟩| ≤ 1` we get `⟨σ^B⟩ ≤ 1`. -/
theorem correlationJ_le_one (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (B : Finset ι) (J : ℝ) :
    correlationJ G h β B J ≤ 1 :=
  le_trans (le_abs_self _) (abs_correlation_le_one G ⟨J, h, β⟩ B)

/-- **Theorem 4.2.3** (Glimm–Jaffe, p. 59):
The correlation function converges as J → ∞ along natural numbers.

For ferromagnetic parameters (`h ≥ 0`, `β > 0`), the sequence
`n ↦ ⟨σ^B⟩_{(G, n, h, β)}` is monotone increasing (by Prop 4.2.1)
and bounded above by 1 (by Prop 4.2.2), hence convergent by
the monotone convergence theorem. The limit equals the supremum
`⨆ n, ⟨σ^B⟩_{(G, n, h, β)}`. -/
theorem correlation_convergent (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (B : Finset ι) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => correlationJ G h β B n)
      Filter.atTop (nhds L) := by
  -- Step 1: The sequence is monotone (Proposition 4.2.1)
  have hmono : Monotone (fun n : ℕ => correlationJ G h β B n) := by
    intro a b hab
    exact correlation_monotone_J G h hh β hβ B
      (Set.mem_Ici.mpr (Nat.cast_nonneg a))
      (Set.mem_Ici.mpr (Nat.cast_nonneg b))
      (Nat.cast_le.mpr hab)
  -- Step 2: The sequence is bounded above by 1 (Proposition 4.2.2)
  have hbdd : BddAbove (Set.range (fun n : ℕ => correlationJ G h β B n)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ correlationJ_le_one G h β B n⟩
  -- Step 3: Monotone + bounded above → convergent (to the supremum)
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩


end IsingModel
