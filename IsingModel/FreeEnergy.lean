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

/-! ## Partition function and free energy monotonicity in J

The same technique as h-monotonicity: reweight by
`R(σ) = exp(β(J₂-J₁) Σ_e edgeSpin(σ,e))`, use `exp(x) ≥ 1+x`,
and apply GKS-I (`⟨σ_iσ_j⟩ ≥ 0`) for each edge. -/

/-- The reweighting identity for the partition function in `J`:
`Z(J₂) = Σ_σ R(σ) · w₁(σ)` where `R = exp(β(J₂-J₁) Σ edgeSpin)`. -/
private theorem partitionFunction_reweight_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (J₁ J₂ : ℝ) :
    partitionFunction G ⟨J₂, h, β⟩ =
    ∑ σ : Config ι,
      (∏ e ∈ G.edgeFinset, Real.exp (β * (J₂ - J₁) * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G ⟨J₁, h, β⟩ σ := by
  unfold partitionFunction boltzmannWeight
  congr 1; ext σ
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  unfold hamiltonian interactionEnergy externalFieldEnergy
  simp only [← Finset.mul_sum]; ring

/-- The partition function is monotone increasing in `J` on `[0, ∞)`.

For `0 ≤ J₁ ≤ J₂`, `h ≥ 0`, `β > 0`:
`Z(J₁, h, β) ≤ Z(J₂, h, β)`.

Proof: same as h-monotonicity. `R(σ) = exp(β(J₂-J₁) Σ edgeSpin)`,
`exp(x) ≥ 1+x` gives `R ≥ 1 + β(J₂-J₁) Σ_e edgeSpin_e(σ)`,
and GKS-I gives `⟨edgeSpin_e⟩ = ⟨σ_iσ_j⟩ ≥ 0`. -/
theorem partitionFunction_monotone_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) (J₁ J₂ : ℝ)
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    partitionFunction G ⟨J₁, h, β⟩ ≤ partitionFunction G ⟨J₂, h, β⟩ := by
  let K := β * (J₂ - J₁)
  have hferm : Ferromagnetic (⟨J₁, h, β⟩ : IsingParams ℝ) := ⟨hJ₁, hh, hβ⟩
  rw [partitionFunction_reweight_J G h β J₁ J₂]
  -- R(σ) = ∏ exp(K edgeSpin) = exp(K Σ edgeSpin) ≥ 1 + K Σ edgeSpin
  have hRexp : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, Real.exp (K * edgeSpin (K := ℝ) σ e)) =
      Real.exp (∑ e ∈ G.edgeFinset, K * edgeSpin (K := ℝ) σ e) := fun σ => by
    rw [← Real.exp_sum]
  have hexp_lb : ∀ σ : Config ι,
      1 + K * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e ≤
        (∏ e ∈ G.edgeFinset, Real.exp (K * edgeSpin (K := ℝ) σ e)) := by
    intro σ; rw [hRexp, ← Finset.mul_sum]
    linarith [Real.add_one_le_exp (K * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)]
  -- Σ R w₁ ≥ Σ (1 + K Σ edgeSpin) w₁
  have hsum_lb : ∑ σ : Config ι,
      (1 + K * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G ⟨J₁, h, β⟩ σ ≤
    ∑ σ : Config ι,
      (∏ e ∈ G.edgeFinset, Real.exp (K * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G ⟨J₁, h, β⟩ σ := by
    apply Finset.sum_le_sum; intro σ _
    exact mul_le_mul_of_nonneg_right (hexp_lb σ) (boltzmannWeight_pos G _ σ).le
  -- Σ (1 + K Σ edgeSpin) w₁ = Z₁ + K Σ_e num_e
  have hexpand : ∑ σ : Config ι,
      (1 + K * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G ⟨J₁, h, β⟩ σ =
    partitionFunction G ⟨J₁, h, β⟩ +
    K * ∑ e ∈ G.edgeFinset, ∑ σ : Config ι,
      edgeSpin (K := ℝ) σ e * boltzmannWeight G ⟨J₁, h, β⟩ σ := by
    unfold partitionFunction
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    apply Finset.sum_congr rfl; intro σ _; ring
  -- Each num_e = Σ edgeSpin_e w₁ ≥ 0 by GKS-I (⟨σ_iσ_j⟩ ≥ 0)
  have hnum_nonneg : ∀ e ∈ G.edgeFinset,
      0 ≤ ∑ σ : Config ι,
        edgeSpin (K := ℝ) σ e * boltzmannWeight G ⟨J₁, h, β⟩ σ := by
    intro e he
    -- Extract endpoints: e = ⟦(i, j)⟧ with i ≠ j
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hij : i ≠ j := by
      intro h; subst h
      exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
    -- edgeSpin σ ⟦(i,j)⟧ = sign(σ i) * sign(σ j) = spinProduct {i,j} σ
    have hedge : ∀ σ : Config ι, edgeSpin (K := ℝ) σ (Quot.mk _ (i, j)) =
        spinProduct {i, j} σ := by
      intro σ; simp [edgeSpin, Sym2.lift, spinProduct, Finset.prod_pair hij, Spin.sign]
    simp_rw [hedge]
    exact (boltzmannWeight_hasNonnegCorrelations G ⟨J₁, h, β⟩ hferm) {i, j}
  -- Combine: Z₁ + K · (non-negative) ≥ Z₁
  calc partitionFunction G ⟨J₁, h, β⟩
      ≤ partitionFunction G ⟨J₁, h, β⟩ +
        K * ∑ e ∈ G.edgeFinset, ∑ σ : Config ι,
          edgeSpin (K := ℝ) σ e * boltzmannWeight G ⟨J₁, h, β⟩ σ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hJ))
          (Finset.sum_nonneg (fun e he => hnum_nonneg e he)))
    _ = ∑ σ : Config ι,
        (1 + K * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e) *
        boltzmannWeight G ⟨J₁, h, β⟩ σ := hexpand.symm
    _ ≤ _ := hsum_lb

/-- The free energy is monotone increasing in `J` on `[0, ∞)`.
Since `Z(J₂) ≥ Z(J₁) > 0`, `ln Z(J₂) ≥ ln Z(J₁)`,
hence `f(J₂) ≥ f(J₁)`. -/
theorem freeEnergy_monotone_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) :
    MonotoneOn (freeEnergyJ G h β) (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJ
  unfold freeEnergyJ freeEnergy
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Real.log_le_log (partitionFunction_pos G ⟨J₁, h, β⟩)
    (partitionFunction_monotone_J G h β hh hβ J₁ J₂ (Set.mem_Ici.mp hJ₁) hJ)

/-! ## Configuration ↔ Finset bijection

The Lee-Yang polynomial sums over subsets `X ⊆ ι` (the "down spin" set),
while the partition function sums over configurations `σ : ι → Spin`.
The bijection is: `σ ↦ {i : σ i = down}` with inverse
`X ↦ fun i => if i ∈ X then down else up`.

This gives the connection identity (Friedli–Velenik, (3.63)–(3.65)):
`Z(J, h, β) = exp(βJ|E| + βhN) · P(z)` where `P = isingEdgePoly`,
`z_i = e^{-2βh}`, `t_e = e^{-2βJ}`. -/

/-- The "down spin" set of a configuration: `{i | σ i = Spin.down}`. -/
def configToFinset (σ : Config ι) : Finset ι :=
  Finset.univ.filter (fun i => σ i = Spin.down)

/-- The configuration corresponding to a subset (down spins). -/
def finsetToConfig (X : Finset ι) : Config ι :=
  fun i => if i ∈ X then Spin.down else Spin.up

/-- `finsetToConfig` is a left inverse of `configToFinset`. -/
@[simp]
theorem finsetToConfig_configToFinset (σ : Config ι) :
    finsetToConfig (configToFinset σ) = σ := by
  ext i; unfold finsetToConfig configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases σ i <;> simp

/-- `configToFinset` is a left inverse of `finsetToConfig`. -/
@[simp]
theorem configToFinset_finsetToConfig (X : Finset ι) :
    configToFinset (finsetToConfig X) = X := by
  ext i; unfold configToFinset finsetToConfig
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split <;> simp_all

/-- The bijection between configurations and subsets (down spin sets). -/
def configFinsetEquiv : Config ι ≃ Finset ι where
  toFun := configToFinset
  invFun := finsetToConfig
  left_inv := finsetToConfig_configToFinset
  right_inv := configToFinset_finsetToConfig

/-! ## Analyticity of the partition polynomial (Theorem 4.6.2, finite volume)

The Lee-Yang circle theorem (`lee_yang_circle`) shows that the Ising
partition polynomial `P(z) = Σ_{X⊆ι} w(X) ∏_{i∈X} z_i` does not vanish
on the open unit polydisk `{z : |z_k| < 1}`.

The connection `Z = exp(βJ|E| + βhN) · P(z)` via `configFinsetEquiv`
shows that `Z ≠ 0` whenever `P ≠ 0`. For the full complex analyticity
(log Z analytic on the polydisk), we need `P(z) ∈ slitPlane`, which
follows from continuity and `P(0) = 1 > 0` via a winding number argument.

Reference: Glimm–Jaffe, Theorem 4.6.2, p. 68;
Friedli–Velenik, (3.63)–(3.65), pp. 122–123. -/

end IsingModel
