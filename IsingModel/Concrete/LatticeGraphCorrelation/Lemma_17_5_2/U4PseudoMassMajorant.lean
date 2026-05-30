import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity

/-!
# `|U_4^∞|` bounded by the pseudo-mass pair-product majorant on ℤ^d (h = 0)

GJ §17.5 Theorem 17.5.1 proof composition (Step 119 plan Step 5.3): the Lebowitz IIIb
absolute-value bound `|U_4^∞| ≤ pair products`
(`truncated4TwoPoint_abs_le_pair_correlations_of_distinct`, PR #3152) composed with the
single-pair pseudo-mass majorant
(`correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair`, PR #3154)
applied to each of the 4 pair correlations yields

    |U_4^∞(0, r, s, u)| ≤ pair-product `pseudoMassG`-majorant.

This is the GJ p. 312 form used to bound the per-summand of the
`∑_z ⟨φ(x₀)φ(z)⟩⟨φ(y₀)φ(z)⟩` Lebowitz IIIb cross-product term by the pseudo-mass majorant.

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §4.3 Cor 4.3.3 p. 86; §17.5 p. 312.
* Issue #1645 (Theorem 17.5.1 / Lemma 17.5.2).
* `.self-local/work/0119-theorem17-5-1-full.md` (Step 119 plan).
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Theorem 17.5.1 Step 5.3: `|U_4^∞|` bounded by pseudo-mass pair-product majorant**
(GJ §4.3 Cor 4.3.3 + §17.5 p. 312, Issue #1645).

For ferromagnetic `⟨J, 0, β⟩` on ℤ^d, with pairwise-distinct `{0, r, s, u}` (and both
pair correlations active in `Ioo 0 2`), the Ursell 4-point function satisfies

    |U_4^∞(0, r, s, u)| ≤ ⟨σ_0σ_s⟩ · ⟨σ_rσ_u⟩ + ⟨σ_0σ_u⟩ · ⟨σ_rσ_s⟩
                       ≤ 2/(1+(m⁻_{0,s}·r')^α) · 2/(1+(m⁻_{r,u}·r')^α)
                         + 2/(1+(m⁻_{0,u}·r')^α) · 2/(1+(m⁻_{r,s}·r')^α)

where `m⁻_{x,y} = pseudoMassFromParamsAtPair hα hr' d (cubicExhaustion d) ⟨J,0,β⟩ x y`
and `r' > 0` is the pseudo-mass radius parameter (denoted `r'` to avoid collision with
the vertex `r`).

Direct composition of `truncated4TwoPoint_abs_le_pair_correlations_of_distinct` (PR #3152)
with the single-pair m⁻ majorant
`correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair` (PR #3154) applied
to each of the 4 pair correlations, followed by `mul_le_mul` for each cross product and
`add_le_add` for the sum with appropriate GKS-I non-negativity. -/
theorem truncated4TwoPoint_abs_le_pseudoMass_majorant_of_distinct
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r') (d : ℕ)
    (J β : ℝ) (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hc_0s : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_ru : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_0u : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_rs : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ∈ Set.Ioo (0 : ℝ) 2) :
    |truncated4TwoPoint d ⟨J, 0, β⟩ r s u| ≤
      2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α) *
        (2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                    (⟨J, 0, β⟩ : IsingParams ℝ) r u * r') ^ α)) +
      2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α) *
        (2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                    (⟨J, 0, β⟩ : IsingParams ℝ) r s * r') ^ α)) := by
  -- Step 1: |U_4| ≤ pair products (PR #3152)
  have h_u4 := truncated4TwoPoint_abs_le_pair_correlations_of_distinct
    d J β hf hr hs hu hrs hru hsu
  -- Step 2: bound each individual correlation by its m⁻ majorant (PR #3154, applied to each)
  have h_0s := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr' (Ambient.cubicExhaustion d) J β (0 : Fin d → ℤ) s hc_0s
  have h_ru := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr' (Ambient.cubicExhaustion d) J β r u hc_ru
  have h_0u := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr' (Ambient.cubicExhaustion d) J β (0 : Fin d → ℤ) u hc_0u
  have h_rs := correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
    hα hr' (Ambient.cubicExhaustion d) J β r s hc_rs
  -- Non-negativities (GKS-I)
  have c_0s_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf _
  have c_ru_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf _
  have c_0u_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf _
  have c_rs_nn : 0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf _
  -- RHS non-negativity (used inside mul_le_mul)
  have hm_0s_nn : 0 ≤ pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s :=
    pseudoMassFromParamsAtPair_nonneg hα hr' d (Ambient.cubicExhaustion d) _ _ _
  have rhs_0s_pos : 0 < 1 + (pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α := by
    have h : 0 ≤ (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α :=
      pow_nonneg (mul_nonneg hm_0s_nn hr'.le) α
    linarith
  have rhs_0s_nn : 0 ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α) :=
    div_nonneg (by norm_num) rhs_0s_pos.le
  have hm_0u_nn : 0 ≤ pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u :=
    pseudoMassFromParamsAtPair_nonneg hα hr' d (Ambient.cubicExhaustion d) _ _ _
  have rhs_0u_pos : 0 < 1 + (pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α := by
    have h : 0 ≤ (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α :=
      pow_nonneg (mul_nonneg hm_0u_nn hr'.le) α
    linarith
  have rhs_0u_nn : 0 ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr' d
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α) :=
    div_nonneg (by norm_num) rhs_0u_pos.le
  -- Two pair-product bounds via mul_le_mul
  have h_prodA :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, u}
        ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α) *
          (2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                      (⟨J, 0, β⟩ : IsingParams ℝ) r u * r') ^ α)) :=
    mul_le_mul h_0s h_ru c_ru_nn rhs_0s_nn
  have h_prodB :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
        ≤ 2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α) *
          (2 / (1 + (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
                      (⟨J, 0, β⟩ : IsingParams ℝ) r s * r') ^ α)) :=
    mul_le_mul h_0u h_rs c_rs_nn rhs_0u_nn
  -- Chain: |U_4| ≤ (pair-products) ≤ (pseudo-mass majorant products)
  exact h_u4.trans (add_le_add h_prodA h_prodB)

/-- **GJ §17.5 Theorem 17.5.1 Step 5.4 capstone: `|U_4^∞|` bounded by polynomial decay form**
(GJ §4.3 Cor 4.3.3 + §17.5 p. 312, Issue #1645 Step 119 plan Step 5.4 capstone).

Compose PR #3156 (`truncated4TwoPoint_abs_le_pseudoMass_majorant_of_distinct`) with PR #3158
(`two_div_one_add_pow_mul_two_div_one_add_pow_le_two_div_pow_mul_two_div_pow`) to bridge the
pseudo-mass pair-product majorant form into the polynomial-decay convolution form. For
ferromagnetic h=0 with pairwise-distinct `{0, r, s, u}`, all 4 pair correlations active, and
the 4 corresponding pseudo-masses strictly positive (so each `m⁻·r' > 0`):

    |U_4^∞(0, r, s, u)| ≤ 2/(m⁻_{0s}·r')^α · 2/(m⁻_{ru}·r')^α
                        + 2/(m⁻_{0u}·r')^α · 2/(m⁻_{rs}·r')^α

This is the **polynomial-decay form** ready for the discrete-HLS sum step
(`tsum_pow_neg_conv_le_const`, Step 130B) over `z` in the GJ p. 312 derivation. -/
theorem truncated4TwoPoint_abs_le_pseudoMass_polynomial_of_distinct
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r') (d : ℕ)
    (J β : ℝ) (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hc_0s : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_ru : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_0u : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_rs : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ∈ Set.Ioo (0 : ℝ) 2)
    (hm_0s_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s)
    (hm_ru_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r u)
    (hm_0u_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u)
    (hm_rs_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r s) :
    |truncated4TwoPoint d ⟨J, 0, β⟩ r s u| ≤
      2 / (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s * r') ^ α *
        (2 / (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) r u * r') ^ α) +
      2 / (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u * r') ^ α *
        (2 / (pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) r s * r') ^ α) := by
  -- Step 1: |U_4| ≤ pseudoMass pair-product majorant (PR #3156)
  have h_u4_maj := truncated4TwoPoint_abs_le_pseudoMass_majorant_of_distinct
    hα hr' d J β hf hr hs hu hrs hru hsu hc_0s hc_ru hc_0u hc_rs
  -- Step 2: pseudoMass pair-product majorant ≤ polynomial decay form (PR #3158, applied twice)
  have h_prodA := two_div_one_add_pow_mul_two_div_one_add_pow_le_two_div_pow_mul_two_div_pow
    (α := α)
    (mul_pos hm_0s_pos hr') (mul_pos hm_ru_pos hr')
  have h_prodB := two_div_one_add_pow_mul_two_div_one_add_pow_le_two_div_pow_mul_two_div_pow
    (α := α)
    (mul_pos hm_0u_pos hr') (mul_pos hm_rs_pos hr')
  -- Chain via add_le_add
  exact h_u4_maj.trans (add_le_add h_prodA h_prodB)

/-- **GJ §17.5 Theorem 17.5.1 |U_4| ≤ r'^{-2α}-factored form** (Step 119 plan Step 5.4
intermediate factorization).

Rewrite of `truncated4TwoPoint_abs_le_pseudoMass_polynomial_of_distinct` (PR #3159) using
the `M^{-2α}` factorization (PR #3160). Each polynomial decay term
`2/(m⁻·r')^α · 2/(m⁻·r')^α` becomes `4·r'^{-2α} · m⁻^{-α} · m⁻^{-α}`, exposing the
common `r'^{-2α}` prefactor and the per-pseudoMass `m⁻^{-α}` decay separately. -/
theorem truncated4TwoPoint_abs_le_pseudoMass_polynomial_factored_of_distinct
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r') (d : ℕ)
    (J β : ℝ) (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hc_0s : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_ru : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_0u : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_rs : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ∈ Set.Ioo (0 : ℝ) 2)
    (hm_0s_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s)
    (hm_ru_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r u)
    (hm_0u_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u)
    (hm_rs_pos : 0 < pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r s) :
    |truncated4TwoPoint d ⟨J, 0, β⟩ r s u| ≤
      4 / r' ^ (2 * α) *
        (1 / pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s ^ α *
         (1 / pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) r u ^ α)) +
      4 / r' ^ (2 * α) *
        (1 / pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u ^ α *
         (1 / pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
              (⟨J, 0, β⟩ : IsingParams ℝ) r s ^ α)) := by
  -- Polynomial decay form from PR #3159
  have h := truncated4TwoPoint_abs_le_pseudoMass_polynomial_of_distinct
    hα hr' d J β hf hr hs hu hrs hru hsu
    hc_0s hc_ru hc_0u hc_rs
    hm_0s_pos hm_ru_pos hm_0u_pos hm_rs_pos
  set m0s : ℝ := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s
  set mru : ℝ := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) r u
  set m0u : ℝ := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u
  set mrs : ℝ := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) r s
  -- Algebraic equality between PR #3159's RHS and this theorem's RHS
  have h_alg : 2 / (m0s * r') ^ α * (2 / (mru * r') ^ α) +
                2 / (m0u * r') ^ α * (2 / (mrs * r') ^ α)
             = 4 / r' ^ (2 * α) * (1 / m0s ^ α * (1 / mru ^ α)) +
                4 / r' ^ (2 * α) * (1 / m0u ^ α * (1 / mrs ^ α)) := by
    have hr'_eq : r' ^ (2 * α) = r' ^ α * r' ^ α := by
      rw [show 2 * α = α + α from by ring, pow_add]
    rw [hr'_eq, mul_pow m0s r' α, mul_pow mru r' α, mul_pow m0u r' α, mul_pow mrs r' α]
    field_simp; norm_num
  rw [h_alg] at h
  exact h

/-- **GJ §17.5 Theorem 17.5.1 |U_4| ≤ uniform-m⁻_inf bound** (Step 119 plan Step 5.5a).

Given a uniform lower bound `m_inf > 0` on all 4 per-pair pseudo-masses
(m⁻_{0s}, m⁻_{ru}, m⁻_{0u}, m⁻_{rs}), the factored polynomial form (PR #3161) consolidates
to a uniform RHS in `m_inf` alone:

    |U_4^∞(0, r, s, u)| ≤ 8 / (r'^(2α) · m_inf^(2α))

This is the GJ p. 312 form ready for the HLS sum over `z` (Step 5.5 capstone): each
per-pair `1/m⁻^α` factor is bounded by `1/m_inf^α` via monotonicity of `t ↦ 1/t^α` on
positive reals, then the 2 same-shape terms sum to give the factor 8 (= 4 + 4).

Mathematically: `m_inf ≤ m⁻_{0s}` and `m_inf > 0` give `m⁻_{0s}^α ≥ m_inf^α > 0`,
hence `1/m⁻_{0s}^α ≤ 1/m_inf^α`. Similarly for the other 3 pseudo-masses. -/
theorem truncated4TwoPoint_abs_le_pseudoMass_uniform_lower_of_distinct
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r') (d : ℕ)
    (J β : ℝ) (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u)
    (hc_0s : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_ru : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_0u : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_rs : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ∈ Set.Ioo (0 : ℝ) 2)
    {m_inf : ℝ} (hm_inf_pos : 0 < m_inf)
    (hm_0s_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s)
    (hm_ru_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r u)
    (hm_0u_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u)
    (hm_rs_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r s) :
    |truncated4TwoPoint d ⟨J, 0, β⟩ r s u| ≤ 8 / (r' ^ (2 * α) * m_inf ^ (2 * α)) := by
  classical
  -- Each pseudo-mass strictly positive (from m_inf > 0 and ≥ m_inf)
  have hm_0s_pos := lt_of_lt_of_le hm_inf_pos hm_0s_ge
  have hm_ru_pos := lt_of_lt_of_le hm_inf_pos hm_ru_ge
  have hm_0u_pos := lt_of_lt_of_le hm_inf_pos hm_0u_ge
  have hm_rs_pos := lt_of_lt_of_le hm_inf_pos hm_rs_ge
  -- Factored polynomial form from PR #3161
  have h := truncated4TwoPoint_abs_le_pseudoMass_polynomial_factored_of_distinct
    hα hr' d J β hf hr hs hu hrs hru hsu
    hc_0s hc_ru hc_0u hc_rs
    hm_0s_pos hm_ru_pos hm_0u_pos hm_rs_pos
  set m0s := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s with hm0s_def
  set mru := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) r u with hmru_def
  set m0u := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u with hm0u_def
  set mrs := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) r s with hmrs_def
  -- Monotonicity: m_inf ≤ m_pair → 1/m_pair^α ≤ 1/m_inf^α
  have hm_inf_pow_pos : 0 < m_inf ^ α := pow_pos hm_inf_pos α
  have h_le : ∀ {m : ℝ}, 0 < m → m_inf ≤ m → 1 / m ^ α ≤ 1 / m_inf ^ α := by
    intro m hm_pos hm_ge
    apply one_div_le_one_div_of_le hm_inf_pow_pos (pow_le_pow_left₀ hm_inf_pos.le hm_ge α)
  have h_0s_le := h_le hm_0s_pos hm_0s_ge
  have h_ru_le := h_le hm_ru_pos hm_ru_ge
  have h_0u_le := h_le hm_0u_pos hm_0u_ge
  have h_rs_le := h_le hm_rs_pos hm_rs_ge
  -- Bound each summand by 4/(r'^(2α) · m_inf^(2α))
  have hr'_pow_pos : 0 < r' ^ (2 * α) := pow_pos hr' (2 * α)
  have hcoef_pos : 0 < 4 / r' ^ (2 * α) := by positivity
  have h_summand : ∀ {ma mb : ℝ}, 0 < ma → 0 < mb → m_inf ≤ ma → m_inf ≤ mb →
      4 / r' ^ (2 * α) * (1 / ma ^ α * (1 / mb ^ α))
        ≤ 4 / r' ^ (2 * α) * (1 / m_inf ^ α * (1 / m_inf ^ α)) := by
    intro ma mb hma_pos hmb_pos hma_ge hmb_ge
    apply mul_le_mul_of_nonneg_left _ hcoef_pos.le
    have hma_le := h_le hma_pos hma_ge
    have hmb_le := h_le hmb_pos hmb_ge
    have hm_inf_pow_inv_nn : 0 ≤ 1 / m_inf ^ α := by positivity
    have hmb_pow_inv_nn : 0 ≤ 1 / mb ^ α := by positivity
    exact mul_le_mul hma_le hmb_le hmb_pow_inv_nn hm_inf_pow_inv_nn
  have h_A := h_summand hm_0s_pos hm_ru_pos hm_0s_ge hm_ru_ge
  have h_B := h_summand hm_0u_pos hm_rs_pos hm_0u_ge hm_rs_ge
  -- Sum gives 8/(r'^(2α) · m_inf^(2α))
  have h_sum_bound :
      4 / r' ^ (2 * α) * (1 / m0s ^ α * (1 / mru ^ α)) +
      4 / r' ^ (2 * α) * (1 / m0u ^ α * (1 / mrs ^ α))
      ≤ 8 / (r' ^ (2 * α) * m_inf ^ (2 * α)) := by
    have h_eq : 4 / r' ^ (2 * α) * (1 / m_inf ^ α * (1 / m_inf ^ α)) +
                  4 / r' ^ (2 * α) * (1 / m_inf ^ α * (1 / m_inf ^ α))
                = 8 / (r' ^ (2 * α) * m_inf ^ (2 * α)) := by
      have : m_inf ^ (2 * α) = m_inf ^ α * m_inf ^ α := by
        rw [show 2 * α = α + α from by ring, pow_add]
      rw [this]
      field_simp; ring
    linarith [h_A, h_B, h_eq.le]
  exact h.trans h_sum_bound

/-- **GJ §17.5 Theorem 17.5.1 finite-sum `∑_u |U_4|` uniform bound** (Step 119 plan
Step 5.5b).

Sum the uniform single-term bound (PR #3165, Step 5.5a) over a Finset of 4th vertices `u`,
assuming the uniform-m_inf lower bound holds for ALL the relevant pseudo-mass instances
across `u ∈ A`. The 4 source vertices `0, r, s` are fixed; `u` ranges over `A`.

For each `u ∈ A` with all 4 pseudo-mass lower bounds and active-pair hypotheses satisfied:

    ∑_{u ∈ A} |U_4^∞(0, r, s, u)| ≤ #A · 8 / (r'^(2α) · m_inf^(2α))

The uniform single-term bound (`8 / (r'^(2α) · m_inf^(2α))`) is independent of `u`, so the
sum is bounded by `#A` times that constant. This is the GJ p. 312 form's preliminary
volume-uniform sum bound. The explicit HLS sum step with per-z polynomial decay
(`tsum_pow_neg_conv_le_const` style refinement) is the subsequent finer step (Step 5.5c). -/
theorem truncated4TwoPoint_sum_abs_le_card_mul_uniform_of_distinct
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r') (d : ℕ)
    (J β : ℝ) (hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    {r s : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s) (hrs : r ≠ s)
    (A : Finset (Fin d → ℤ))
    (hu_ne : ∀ u ∈ A, (0 : Fin d → ℤ) ≠ u ∧ r ≠ u ∧ s ≠ u)
    (hc_0s : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_rs : Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_ru : ∀ u ∈ A,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} ∈ Set.Ioo (0 : ℝ) 2)
    (hc_0u : ∀ u ∈ A,
      Ambient.correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), u} ∈ Set.Ioo (0 : ℝ) 2)
    {m_inf : ℝ} (hm_inf_pos : 0 < m_inf)
    (hm_0s_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) s)
    (hm_rs_ge : m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r s)
    (hm_ru_ge : ∀ u ∈ A,
      m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) r u)
    (hm_0u_ge : ∀ u ∈ A,
      m_inf ≤ pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) (0 : Fin d → ℤ) u) :
    ∑ u ∈ A, |truncated4TwoPoint d ⟨J, 0, β⟩ r s u|
      ≤ A.card • (8 / (r' ^ (2 * α) * m_inf ^ (2 * α))) := by
  classical
  -- Per-element bound: each summand ≤ constant
  have h_summand : ∀ u ∈ A,
      |truncated4TwoPoint d ⟨J, 0, β⟩ r s u| ≤ 8 / (r' ^ (2 * α) * m_inf ^ (2 * α)) := by
    intro u hu
    obtain ⟨h0u_ne, hru_ne, hsu_ne⟩ := hu_ne u hu
    exact truncated4TwoPoint_abs_le_pseudoMass_uniform_lower_of_distinct
      hα hr' d J β hf hr hs h0u_ne hrs hru_ne hsu_ne
      hc_0s (hc_ru u hu) (hc_0u u hu) hc_rs
      hm_inf_pos hm_0s_ge (hm_ru_ge u hu) (hm_0u_ge u hu) hm_rs_ge
  -- Sum bound: ∑_{u ∈ A} bound = #A · bound
  calc ∑ u ∈ A, |truncated4TwoPoint d ⟨J, 0, β⟩ r s u|
      ≤ ∑ _u ∈ A, 8 / (r' ^ (2 * α) * m_inf ^ (2 * α)) :=
        Finset.sum_le_sum h_summand
    _ = A.card • (8 / (r' ^ (2 * α) * m_inf ^ (2 * α))) := by
        rw [Finset.sum_const]

end Ambient
end IsingModel
