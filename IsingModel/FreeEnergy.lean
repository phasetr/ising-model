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

/-- Convert a SimpleGraph's edges to the edge list format used by `lee_yang_circle`.
Each edge `e` is represented as `(e.out.1, e.out.2, t)` with uniform coupling `t`. -/
noncomputable def graphToEdgeList (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) : List (ι × ι × ℝ) :=
  G.edgeFinset.toList.map fun e => ((Quot.out e).1, (Quot.out e).2, t)

omit [Fintype ι] [DecidableEq ι] in
/-- Each entry in `graphToEdgeList` has distinct endpoints. -/
private theorem graphToEdgeList_distinct (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) : ∀ e ∈ graphToEdgeList G t, e.1 ≠ e.2.1 := by
  intro e he
  simp only [graphToEdgeList, List.mem_map, Finset.mem_toList] at he
  obtain ⟨edge, he_mem, he_eq⟩ := he
  have hadj : G.Adj (Quot.out edge).1 (Quot.out edge).2 := by
    have h := SimpleGraph.mem_edgeFinset.mp he_mem
    rwa [show edge = s((Quot.out edge).1, (Quot.out edge).2) from by
      conv_lhs => rw [← Quot.out_eq edge], SimpleGraph.mem_edgeSet] at h
  simp only [← he_eq]; exact hadj.ne

omit [Fintype ι] [DecidableEq ι] in
/-- Each entry in `graphToEdgeList` has coupling in `[0, 1)`. -/
private theorem graphToEdgeList_coupling (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∀ e ∈ graphToEdgeList G t, 0 ≤ e.2.2 ∧ e.2.2 < 1 := by
  intro e he
  simp only [graphToEdgeList, List.mem_map, Finset.mem_toList] at he
  obtain ⟨_, _, he_eq⟩ := he
  simp only [← he_eq]; exact ⟨ht₀, ht₁⟩

/-- **Lee-Yang nonvanishing for the Ising partition polynomial**
(Glimm–Jaffe, §4.5–4.6; Friedli–Velenik, Theorem 3.43, pp. 122–127):

For the Ising model on graph `G` with coupling `t = e^{-2βJ}` (`0 ≤ t < 1`,
i.e., `J > 0`), the partition polynomial `P(z)` does not vanish on the
open unit polydisk `{z : |z_k| < 1}`. Here `z_k = e^{-2βh_k}` is the
fugacity at site `k`.

This is the finite-volume version of Theorem 4.6.2: since
`Z = exp(βJ|E| + βhN) · P(z)` and `exp(...) > 0`, the nonvanishing
of `P` is equivalent to `Z ≠ 0`. -/
theorem isingEdgePoly_nonvanishing_of_graph
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (isingEdgePoly (graphToEdgeList G t)).eval z ≠ 0 :=
  lee_yang_circle _ (graphToEdgeList_distinct G t) (graphToEdgeList_coupling G t ht₀ ht₁) z hz

/-! ## Analyticity of the free energy (Theorem 4.6.2)

The free energy `f(h) = |ι|⁻¹ ln Z(h)` is real-analytic in the external
field `h` on `(0, ∞)`.

The proof strategy:
1. Each Boltzmann weight `w(σ, h) = exp(a(σ) + b(σ)·h)` is real-analytic in `h`
   (exponential of an affine function).
2. `Z(h) = Σ_σ w(σ, h)` is a finite sum of real-analytic functions, hence
   real-analytic.
3. `Z(h) > 0` for all `h` (`partitionFunction_pos`).
4. `ln Z(h)` is real-analytic where `Z > 0` (`AnalyticAt.log`).
5. `f(h) = |ι|⁻¹ · ln Z(h)` is real-analytic.

Reference: Glimm–Jaffe, *Quantum Physics*, §4.6, Theorem 4.6.2, pp. 67–70.
The finite-volume real-analyticity is the starting point for the complex
analyticity established via Lee-Yang and Vitali convergence. -/

omit [DecidableEq ι] in
/-- Each Boltzmann weight is real-analytic in `h` (exponential of affine). -/
private theorem boltzmannWeight_analyticAt_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) (h₀ : ℝ) :
    AnalyticAt ℝ (fun h => boltzmannWeight G ⟨J, h, β⟩ σ) h₀ := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only
  fun_prop

/-- The partition function is real-analytic in the external field `h`.
`Z(h) = Σ_σ exp(a(σ) + b(σ)·h)` is a finite sum of real-analytic
functions, hence real-analytic. -/
theorem partitionFunctionH_analyticAt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (h₀ : ℝ) :
    AnalyticAt ℝ (fun h => partitionFunction G ⟨J, h, β⟩) h₀ := by
  unfold partitionFunction
  exact Finset.analyticAt_fun_sum _ (fun σ _ =>
    boltzmannWeight_analyticAt_h G J β σ h₀)

/-- **Theorem 4.6.2** (Glimm–Jaffe, §4.6, p. 68, finite-volume real version).
The free energy per site `f(h) = |ι|⁻¹ ln Z(h)` is real-analytic in the
external field `h` on `(0, ∞)`.

Since `Z(h) > 0` for all `h`, `ln Z(h)` is defined and real-analytic.
The restriction to `h > 0` matches the domain of the complex analyticity
in Theorem 4.6.2 (where `|Im h| < Re h` gives `Re h > 0`). -/
theorem freeEnergyH_analyticOn
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    AnalyticOn ℝ (freeEnergyH G J β) (Set.Ioi 0) := by
  intro h₀ hh₀
  unfold freeEnergyH freeEnergy
  exact (analyticAt_const.mul
    ((partitionFunctionH_analyticAt G J β h₀).log
      (partitionFunction_pos G ⟨J, h₀, β⟩))).analyticWithinAt

omit [DecidableEq ι] in
/-- Each Boltzmann weight is real-analytic in `J` (exponential of affine). -/
private theorem boltzmannWeight_analyticAt_J
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (σ : Config ι) (J₀ : ℝ) :
    AnalyticAt ℝ (fun J => boltzmannWeight G ⟨J, h, β⟩ σ) J₀ := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only
  fun_prop

/-- The partition function is real-analytic in the coupling constant `J`. -/
theorem partitionFunctionJ_analyticAt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (J₀ : ℝ) :
    AnalyticAt ℝ (fun J => partitionFunction G ⟨J, h, β⟩) J₀ := by
  unfold partitionFunction
  exact Finset.analyticAt_fun_sum _ (fun σ _ =>
    boltzmannWeight_analyticAt_J G h β σ J₀)

/-- The free energy is real-analytic in `J` on `(0, ∞)`.
Since `Z > 0` always holds, `ln Z(J)` is defined and real-analytic. -/
theorem freeEnergyJ_analyticOn
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    AnalyticOn ℝ (freeEnergyJ G h β) (Set.Ioi 0) := by
  intro J₀ _
  unfold freeEnergyJ freeEnergy
  exact (analyticAt_const.mul
    ((partitionFunctionJ_analyticAt G h β J₀).log
      (partitionFunction_pos G ⟨J₀, h, β⟩))).analyticWithinAt

/-! ## Free energy infinite volume convergence (Proposition 4.6.1)

For a ferromagnetic Ising model on a fixed ambient finite lattice `ι`,
the free energy `f_G = |ι|⁻¹ ln Z_G` is monotone along the subgraph
order and bounded above (by `f_⊤` on the complete ambient graph),
hence converges for any increasing sequence of subgraphs.

This is a *discretized* formalization of Glimm–Jaffe Proposition 4.6.1
(p. 68): "Let Z_Λ denote the partition function for a lattice field
with nearest-neighbor, translation-invariant, ferromagnetic pair
interaction; with single-spin distribution satisfying (4.1.4). As
Λ ↑ ∞, f_Λ = |Λ|⁻¹ ln Z_Λ converges". The original statement is
for an infinite ambient lattice with finite-volume exhaustions; our
formalization uses a fixed finite ambient lattice with growing subgraphs.
The proof mechanism (monotonicity + boundedness) is the same.

Note: GJ's Prop 4.6.1 is a general lattice-spin result, not Ising-only;
the Ising model is a special case where the single-spin distribution
is the symmetric Bernoulli measure on `{±1}`. -/

/-- The partition function is monotone in the subgraph order.
For `G₁ ≤ G₂` and ferromagnetic `p`, `Z_{G₁} ≤ Z_{G₂}`.

Proof: Factor `w_{G₂} = R · w_{G₁}` where
`R(σ) = ∏_{e ∈ E(G₂)\E(G₁)} exp(βJ · edgeSpin σ e)`.
Use `exp(x) ≥ 1 + x` and GKS-I (each `⟨σᵢσⱼ⟩_{G₁} ≥ 0`)
to bound `∑ R · w_{G₁} ≥ Z_{G₁}`. -/
theorem partitionFunction_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunction G₁ p ≤ partitionFunction G₂ p := by
  have hfact : ∀ σ, boltzmannWeight G₂ p σ =
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G₁ p σ :=
    fun σ => boltzmannWeight_subgraph_factor h₁₂ p σ
  have hZ : partitionFunction G₂ p =
      ∑ σ : Config ι,
        (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
        boltzmannWeight G₁ p σ := by
    unfold partitionFunction
    apply Finset.sum_congr rfl; intro σ _; exact hfact σ
  rw [hZ]
  have hR_lb : ∀ σ : Config ι,
      1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e ≤
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) := by
    intro σ
    rw [← Real.exp_sum]
    simp_rw [← Finset.mul_sum]
    linarith [Real.add_one_le_exp (p.β * p.J *
      ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset, edgeSpin (K := ℝ) σ e)]
  have hsum_lb : ∑ σ : Config ι,
      (1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G₁ p σ ≤
    ∑ σ : Config ι,
      (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        Real.exp (p.β * p.J * edgeSpin (K := ℝ) σ e)) *
      boltzmannWeight G₁ p σ := by
    apply Finset.sum_le_sum; intro σ _
    exact mul_le_mul_of_nonneg_right (hR_lb σ) (boltzmannWeight_pos G₁ p σ).le
  have hexpand : ∑ σ : Config ι,
      (1 + p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
        edgeSpin (K := ℝ) σ e) *
      boltzmannWeight G₁ p σ =
    partitionFunction G₁ p +
    p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      ∑ σ : Config ι, edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ := by
    unfold partitionFunction
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    apply Finset.sum_congr rfl; intro σ _; ring
  have hnum_nonneg : ∀ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
      0 ≤ ∑ σ : Config ι,
        edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ := by
    intro e he
    have he₂ : e ∈ G₂.edgeFinset := (Finset.mem_sdiff.mp he).1
    obtain ⟨⟨i, j⟩, rfl⟩ := Quot.exists_rep e
    have hij : i ≠ j := by
      intro h; subst h
      exact (SimpleGraph.mem_edgeFinset.mp he₂).ne rfl
    have hedge : ∀ σ : Config ι, edgeSpin (K := ℝ) σ (Quot.mk _ (i, j)) =
        spinProduct {i, j} σ := by
      intro σ; simp [edgeSpin, Sym2.lift, spinProduct, Finset.prod_pair hij, Spin.sign]
    simp_rw [hedge]
    exact (boltzmannWeight_hasNonnegCorrelations G₁ p hf) {i, j}
  calc partitionFunction G₁ p
      ≤ partitionFunction G₁ p +
        p.β * p.J * ∑ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          ∑ σ : Config ι, edgeSpin (K := ℝ) σ e * boltzmannWeight G₁ p σ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
          (Finset.sum_nonneg (fun e he => hnum_nonneg e he)))
    _ = _ := hexpand.symm
    _ ≤ _ := hsum_lb

/-- The logarithm of the partition function is monotone in the subgraph
order: for `G₁ ≤ G₂` and ferromagnetic `p`,
`log Z_{G₁} p ≤ log Z_{G₂} p`. Consolidates the
`Real.log_le_log ∘ partitionFunction_monotone_subgraph` pattern. -/
theorem log_partitionFunction_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunction G₁ p) ≤ Real.log (partitionFunction G₂ p) :=
  Real.log_le_log (partitionFunction_pos G₁ p)
    (partitionFunction_monotone_subgraph h₁₂ p hf)

/-- The free energy is monotone in the subgraph order.
Follows from `log_partitionFunction_monotone_subgraph` after multiplying
by `|ι|⁻¹ ≥ 0`. -/
theorem freeEnergy_monotone_subgraph
    {G₁ G₂ : SimpleGraph ι} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergy G₁ p ≤ freeEnergy G₂ p := by
  unfold freeEnergy
  exact mul_le_mul_of_nonneg_left
    (log_partitionFunction_monotone_subgraph h₁₂ p hf)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **Unconditional lower bound `Z_⊥ ≥ 1` on the empty graph.**

Since `partitionFunction_bot` gives `Z_⊥ = (2·cosh(β h))^|ι|` and
`Real.one_le_cosh` is unconditional, we have `2·cosh(β h) ≥ 2 ≥ 1`,
and `(...)^|ι| ≥ 1`. No ferromagnetic hypothesis required. -/
theorem partitionFunction_bot_ge_one (p : IsingParams ℝ) :
    (1 : ℝ) ≤ partitionFunction (⊥ : SimpleGraph ι) p := by
  have h_cosh_ge : 1 ≤ 2 * Real.cosh (p.β * p.h) := by
    have : 1 ≤ Real.cosh (p.β * p.h) := Real.one_le_cosh _
    linarith
  have h_pow : 1 ≤ (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    one_le_pow₀ h_cosh_ge
  rw [partitionFunction_bot]
  exact h_pow

/-- **Lower bound `Z_G ≥ 1` for ferromagnetic parameters.**

The ferromagnetic hypothesis is used only to transport the
unconditional `⊥`-graph bound to `G` via
`partitionFunction_monotone_subgraph`:
`Z_G ≥ Z_⊥ ≥ 1`. Used downstream as the companion to the §4.6
super-additivity inequality: because `log Z_G ≥ 0` (ferromagnetic),
the disjoint-sum chain
`log Z_{Λ₁} + log Z_{Δ} ≤ log Z_{Λ₁ ∪ Δ}` upgrades to subset-wise
monotonicity `log Z_{Λ₁} ≤ log Z_{Λ₁ ∪ Δ}` for any `Δ` disjoint
from `Λ₁`. -/
theorem partitionFunction_ge_one_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    1 ≤ partitionFunction G p :=
  (partitionFunction_bot_ge_one p).trans
    (partitionFunction_monotone_subgraph bot_le p hf)

/-- Logarithmic form: `log Z_G ≥ 0` for ferromagnetic parameters.

Immediate from `partitionFunction_ge_one_of_ferromagnetic` and
`Real.log_nonneg`. -/
theorem log_partitionFunction_nonneg_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunction G p) :=
  Real.log_nonneg (partitionFunction_ge_one_of_ferromagnetic G p hf)

/-- **Basic identity** `|ι| · freeEnergy G p = log (partitionFunction G p)`
for `0 < |ι|`.

Unfolds the definition `freeEnergy = |ι|⁻¹ · log Z` and cancels the
`|ι|⁻¹` prefactor against the outer `|ι|` via `field_simp`.
The nonempty hypothesis rules out the `|ι| = 0` degenerate case.

Base-layer analog of PR #119's
`card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty`. -/
theorem card_mul_freeEnergy_eq_log_partitionFunction
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * freeEnergy G p
      = Real.log (partitionFunction G p) := by
  unfold freeEnergy
  have hne_card : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hne.ne'
  field_simp

/-- **Unconditional `⊥`-graph bound `Z_⊥ ≥ 2^|ι|`.**

From `partitionFunction_bot = (2 · cosh(βh))^|ι|` and
`Real.one_le_cosh`, hence `2 ≤ 2 · cosh(βh)`, hence
`2^|ι| ≤ (2 · cosh(βh))^|ι|`. No ferromagnetic hypothesis
required. -/
theorem partitionFunction_bot_ge_two_pow_card (p : IsingParams ℝ) :
    (2 : ℝ) ^ Fintype.card ι ≤ partitionFunction (⊥ : SimpleGraph ι) p := by
  have h_cosh_ge : (2 : ℝ) ≤ 2 * Real.cosh (p.β * p.h) := by
    have : 1 ≤ Real.cosh (p.β * p.h) := Real.one_le_cosh _
    linarith
  have h_pow : (2 : ℝ) ^ Fintype.card ι
      ≤ (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    pow_le_pow_left₀ (by norm_num) h_cosh_ge _
  rw [partitionFunction_bot]
  exact h_pow

/-- **Strong ferromagnetic lower bound `Z_G ≥ 2^|ι|`.**

Combines `partitionFunction_bot_ge_two_pow_card` with
`partitionFunction_monotone_subgraph`: `2^|ι| ≤ Z_⊥ ≤ Z_G`.
Strictly sharper than `partitionFunction_ge_one_of_ferromagnetic`
when `|ι| ≥ 1`. Used to derive `log Z_G ≥ |ι| · log 2` (the
sharp version of `≥ 0`). -/
theorem partitionFunction_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Fintype.card ι ≤ partitionFunction G p :=
  (partitionFunction_bot_ge_two_pow_card p).trans
    (partitionFunction_monotone_subgraph bot_le p hf)

/-- **Sharp ferromagnetic lower bound (non-log form)**:
`(2·cosh(βh))^|ι| ≤ Z_G(p)`.

Direct from `partitionFunction_bot` (`Z_⊥ = (2·cosh(βh))^|ι|`) and
`partitionFunction_monotone_subgraph` (`bot ≤ G`, ferromagnetic).
Sharpening of `partitionFunction_ge_two_pow_card_of_ferromagnetic`
(since `cosh ≥ 1`); the exp-image of PR #173
`log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic`. -/
theorem partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι ≤ partitionFunction G p := by
  calc (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι
      = partitionFunction (⊥ : SimpleGraph ι) p := (partitionFunction_bot p).symm
    _ ≤ partitionFunction G p := partitionFunction_monotone_subgraph bot_le p hf

/-- Logarithmic form: `log Z_G ≥ |ι| · log 2` for ferromagnetic.

Immediate from `partitionFunction_ge_two_pow_card_of_ferromagnetic`
via `Real.log_pow` + `Real.log_le_log`. -/
theorem log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card ι : ℝ) * Real.log 2 ≤ Real.log (partitionFunction G p) := by
  have h_two_pow_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  have h_log :=
    Real.log_le_log h_two_pow_pos
      (partitionFunction_ge_two_pow_card_of_ferromagnetic G p hf)
  rw [Real.log_pow] at h_log
  exact h_log

/-- **Sharp ferromagnetic log-Z lower bound**:
`|ι| · log(2·cosh(βh)) ≤ log Z_G(p)`.

Sharpening of `log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic`
via `Z_⊥ = (2·cosh(βh))^|ι|` (from `partitionFunction_bot`) and
`Z_⊥ ≤ Z_G` (ferromagnetic `partitionFunction_monotone_subgraph`);
take `log` + `Real.log_pow`. -/
theorem log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Fintype.card ι : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunction G p) := by
  have h_cosh_pos : (0 : ℝ) < 2 * Real.cosh (p.β * p.h) := by
    have := Real.one_le_cosh (p.β * p.h); linarith
  have h_pow_pos : (0 : ℝ) < (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι :=
    pow_pos h_cosh_pos _
  have h_ge : (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι
      ≤ partitionFunction G p := by
    rw [← partitionFunction_bot (p := p)]
    exact partitionFunction_monotone_subgraph bot_le p hf
  have h_log := Real.log_le_log h_pow_pos h_ge
  rw [Real.log_pow] at h_log
  exact h_log

/-- The free energy rescaling identity in `β`:
`f(J, h, β) = f(βJ, βh, 1)`. Follows from `partitionFunction_beta_rescale`
(after taking `log` and multiplying by `|ι|⁻¹`). -/
private theorem freeEnergy_rescale_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G ⟨J, h, β⟩ = freeEnergy G ⟨β * J, β * h, 1⟩ := by
  unfold freeEnergy
  congr 1
  have hw : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, h, β⟩ σ = boltzmannWeight G ⟨β * J, β * h, 1⟩ σ := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1; ring
  unfold partitionFunction
  simp_rw [hw]

/-- **Free energy β-monotonicity**: for `J, h ≥ 0`, the free energy per
site is monotone increasing in the inverse temperature `β` on `(0, ∞)`.

Proof: Apply the rescaling identity `freeEnergy_rescale_beta` and
combine `freeEnergy_monotone_J` and `freeEnergy_monotone_h`. -/
theorem freeEnergy_monotone_beta (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) :
    MonotoneOn (fun β : ℝ => freeEnergy G ⟨J, h, β⟩) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβ
  change freeEnergy G ⟨J, h, β₁⟩ ≤ freeEnergy G ⟨J, h, β₂⟩
  rw [freeEnergy_rescale_beta G J h β₁, freeEnergy_rescale_beta G J h β₂]
  have hβ₁' : 0 < β₁ := hβ₁
  have hβ₂' : 0 < β₂ := lt_of_lt_of_le hβ₁' hβ
  have hβ₁J : 0 ≤ β₁ * J := mul_nonneg hβ₁'.le hJ
  have hβ₂J : 0 ≤ β₂ * J := mul_nonneg hβ₂'.le hJ
  have hβ₁h : 0 ≤ β₁ * h := mul_nonneg hβ₁'.le hh
  have hβ₂h : 0 ≤ β₂ * h := mul_nonneg hβ₂'.le hh
  calc freeEnergy G ⟨β₁ * J, β₁ * h, 1⟩
      ≤ freeEnergy G ⟨β₂ * J, β₁ * h, 1⟩ := by
        have := freeEnergy_monotone_J G (β₁ * h) 1 hβ₁h one_pos
          (Set.mem_Ici.mpr hβ₁J) (Set.mem_Ici.mpr hβ₂J)
          (mul_le_mul_of_nonneg_right hβ hJ)
        exact this
    _ ≤ freeEnergy G ⟨β₂ * J, β₂ * h, 1⟩ := by
        have := freeEnergy_monotone_h G (β₂ * J) 1 hβ₂J one_pos
          (Set.mem_Ici.mpr hβ₁h) (Set.mem_Ici.mpr hβ₂h)
          (mul_le_mul_of_nonneg_right hβ hh)
        exact this

/-- **Proposition 4.6.1** (Glimm–Jaffe, p. 68): The free energy converges
along any increasing sequence of subgraphs on a fixed ambient finite lattice.

The free energy `n ↦ f_{Gₙ}` is monotone (by `freeEnergy_monotone_subgraph`)
and bounded above by `f_⊤` (free energy on the complete graph, via
`le_top`), hence converges to its supremum by `tendsto_atTop_ciSup`. -/
theorem freeEnergy_convergent_subgraph
    (Gn : ℕ → SimpleGraph ι) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => freeEnergy (Gn n) p)
      Filter.atTop (nhds L) := by
  have h_mono : Monotone (fun n : ℕ => freeEnergy (Gn n) p) :=
    fun a b hab => freeEnergy_monotone_subgraph (hmono hab) p hf
  have h_bdd : BddAbove (Set.range (fun n : ℕ => freeEnergy (Gn n) p)) :=
    ⟨freeEnergy (⊤ : SimpleGraph ι) p,
     fun _ ⟨n, hn⟩ => hn ▸ freeEnergy_monotone_subgraph le_top p hf⟩
  exact ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

/-- **Free energy at zero parameters**: for nonempty lattice `ι` with
`0 < Fintype.card ι`, `freeEnergy G ⟨0, 0, β⟩ = log 2`.

Combines `partitionFunction_zero_params` (Z = |Config ι|) with
`card_config_eq_two_pow` (|Config ι| = 2^|ι|) and
`Real.log_pow` (log(2^|ι|) = |ι| · log 2); the `|ι|⁻¹` prefix then
cancels to give `log 2`. -/
theorem freeEnergy_zero_params (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergy
  rw [partitionFunction_zero_params, card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy on the empty graph** (free-spin / one-body limit):
for nonempty `ι`,
`freeEnergy (⊥ : SimpleGraph ι) p = log (2 · cosh(β · h))`.

Combines `partitionFunction_bot` (`Z = (2 cosh(β h))^|ι|`) with
`Real.log_pow` (`log(a^n) = n · log a`, valid here since
`2 cosh(β h) > 0`); the `|ι|⁻¹` prefix then cancels to give
`log (2 cosh(β h))`.

Complements `freeEnergy_zero_params` (the `J = h = 0` point, where
`cosh 0 = 1` recovers `log 2`) by extending to arbitrary `h` on the
J-less graph. -/
theorem freeEnergy_bot (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy (⊥ : SimpleGraph ι) p
      = Real.log (2 * Real.cosh (p.β * p.h)) := by
  unfold freeEnergy
  rw [partitionFunction_bot, Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy h-symmetry**: `freeEnergy G ⟨J, -h, β⟩ = freeEnergy G ⟨J, h, β⟩`.

Immediate from `partitionFunction_neg_h` (spin-flip reindexing) by
taking `log` and dividing by `|ι|`. -/
theorem freeEnergy_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergy
  rw [partitionFunction_neg_h]

/-- **Free energy equals its value at `|h|`**:
`freeEnergy G ⟨J, h, β⟩ = freeEnergy G ⟨J, |h|, β⟩`.

Case-split on `|h| = h ∨ |h| = -h` and apply `freeEnergy_neg_h` when
needed. -/
theorem freeEnergy_eq_abs_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergy G (⟨J, |h|, β⟩ : IsingParams ℝ) := by
  rcases abs_choice h with habs | habs
  · rw [habs]
  · rw [habs, freeEnergy_neg_h]

/-- **Free energy is monotone in `|h|`** for ferromagnetic parameters:
`|h₁| ≤ |h₂| → freeEnergy G ⟨J, h₁, β⟩ ≤ freeEnergy G ⟨J, h₂, β⟩`.

Combines `freeEnergy_eq_abs_h` (h-even) with `freeEnergy_monotone_h`
on `[0, ∞)`: rewrite both sides as `freeEnergy G ⟨J, |hᵢ|, β⟩` and
apply the `Ici 0` monotonicity using `abs_nonneg`. -/
theorem freeEnergy_monotone_abs_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergy G (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergy G (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [freeEnergy_eq_abs_h G J h₁ β, freeEnergy_eq_abs_h G J h₂ β]
  have := freeEnergy_monotone_h G J β hJ hβ
    (Set.mem_Ici.mpr (abs_nonneg h₁))
    (Set.mem_Ici.mpr (abs_nonneg h₂)) hh
  exact this

/-- **Partition function is monotone in `|h|`** for ferromagnetic parameters:
`|h₁| ≤ |h₂| → Z(J, h₁, β) ≤ Z(J, h₂, β)`.

Combines `partitionFunction_eq_abs_h` (Z even in h) with
`partitionFunction_monotone_h` on `[0, ∞)`. Z-level counterpart of
`freeEnergy_monotone_abs_h`. -/
theorem partitionFunction_monotone_abs_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunction G (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunction G (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [partitionFunction_eq_abs_h G J h₁ β,
      partitionFunction_eq_abs_h G J h₂ β]
  exact partitionFunction_monotone_h G J β hJ hβ _ _ (abs_nonneg h₁) hh

/-- **Free energy at `β = 0`**: for nonempty `ι` and any `J, h : ℝ`,
`freeEnergy G ⟨J, h, 0⟩ = log 2`.

Corollary of `partitionFunction_beta_zero` (`Z = |Config ι| = 2^|ι|`),
taking `log` and dividing by `|ι|`. β-direction analogue of
`freeEnergy_zero_params` (`J = h = 0`), holds for any ambient `G`. -/
theorem freeEnergy_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergy
  rw [partitionFunction_beta_zero, card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hne.ne'
  field_simp

/-- **Free energy on the empty graph at zero field**: for nonempty `ι`
and any `J, β : ℝ`,
`freeEnergy (⊥ : SimpleGraph ι) ⟨J, 0, β⟩ = log 2`.

Corollary of `freeEnergy_bot` at `h = 0` (`cosh 0 = 1`, `log(2·1) = log 2`).
Consistent with `freeEnergy_zero_params` (`J = h = 0`) and shows that on
the J-less graph the coupling `J` is dormant. -/
theorem freeEnergy_bot_h_zero (J β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy (⊥ : SimpleGraph ι) (⟨J, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 := by
  rw [freeEnergy_bot _ hne]
  simp [Real.cosh_zero]

/-- **Graph-independent free energy identity at `J = 0`**:
`freeEnergy G ⟨0, h, β⟩ = freeEnergy ⊥ ⟨0, h, β⟩`.

Immediate from `partitionFunction_eq_bot_at_J_zero` after unfolding
`freeEnergy := |ι|⁻¹ · log Z`. -/
theorem freeEnergy_eq_bot_at_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    freeEnergy G (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergy (⊥ : SimpleGraph ι) (⟨0, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergy
  rw [partitionFunction_eq_bot_at_J_zero]

/-- **Free energy at `J = 0`** (graph-independent): for nonempty `ι`,
any `h, β : ℝ`, and any ambient graph `G`,
`freeEnergy G ⟨0, h, β⟩ = log (2·cosh(β·h))`.

Combines `freeEnergy_eq_bot_at_J_zero` (graph independence) with
`freeEnergy_bot` (`⊥` closed form). -/
theorem freeEnergy_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  (freeEnergy_eq_bot_at_J_zero G h β).trans (freeEnergy_bot _ hne)

/-- **Sharp ferromagnetic lower bound**: for any graph `G` with
`|ι| > 0` and ferromagnetic parameters, `log(2·cosh(β·h)) ≤ freeEnergy G p`.

Obtained from `freeEnergy_bot` (free-spin closed form) and
`freeEnergy_monotone_subgraph` (ferromagnetic, `⊥ ≤ G` via `bot_le`).
Sharpens `log 2` (since `cosh(β h) ≥ 1`, with equality at `h = 0`). -/
theorem freeEnergy_ge_log_two_cosh (G : SimpleGraph ι) [Fintype G.edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (hne : 0 < Fintype.card ι) :
    Real.log (2 * Real.cosh (β * h)) ≤ freeEnergy G ⟨J, h, β⟩ := by
  have hferm : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ) := ⟨hJ, hh, hβ⟩
  calc Real.log (2 * Real.cosh (β * h))
      = freeEnergy (⊥ : SimpleGraph ι) (⟨J, h, β⟩ : IsingParams ℝ) := by
        rw [freeEnergy_bot _ hne]
    _ ≤ freeEnergy G (⟨J, h, β⟩ : IsingParams ℝ) :=
        freeEnergy_monotone_subgraph bot_le _ hferm

/-- **Free energy lower bound `log 2 ≤ f_G(p)` for ferromagnetic.**

Weaker than `freeEnergy_ge_log_two_cosh` (which uses the sharp
`log (2 · cosh(β h))` bound) but doesn't depend on the specific form of
`p`; takes a `Ferromagnetic p` hypothesis uniformly.

Via `Real.one_le_cosh`, `2 · cosh(β h) ≥ 2`, so
`log 2 ≤ log (2 · cosh(β h))` by log-monotonicity; then compose with
`freeEnergy_ge_log_two_cosh`. -/
theorem freeEnergy_ge_log_two_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hne : 0 < Fintype.card ι) :
    Real.log 2 ≤ freeEnergy G p := by
  obtain ⟨J, h, β⟩ := p
  have h_cosh : 1 ≤ Real.cosh (β * h) := Real.one_le_cosh _
  have h_log : Real.log 2 ≤ Real.log (2 * Real.cosh (β * h)) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    linarith
  exact h_log.trans (freeEnergy_ge_log_two_cosh G hf.hJ hf.hh hf.hβ hne)

/-- **Nonnegativity `0 ≤ f_G(p)` for ferromagnetic parameters** on
nonempty `ι`. Immediate from
`freeEnergy_ge_log_two_of_ferromagnetic` and `Real.log_pos`
(`0 < log 2`). -/
theorem freeEnergy_nonneg_of_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G p :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans
    (freeEnergy_ge_log_two_of_ferromagnetic G p hf hne)

end IsingModel
