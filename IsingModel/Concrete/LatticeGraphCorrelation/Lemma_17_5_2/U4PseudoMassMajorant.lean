import IsingModel.Concrete.LatticeGraphCorrelation.InfiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity

/-!
# `|U_4^∞|` bounded by the pseudo-mass pair-product majorant on ℤ^d (h = 0)

GJ §17.5 Theorem 17.5.1 proof composition (Step 119 plan Step 5.3): the Lebowitz IIIb
absolute-value bound `|U_4^∞| ≤ pair products`
(`truncated4TwoPoint_abs_le_pair_correlations_of_distinct`, PR #3152) composed with the
single-pair pseudo-mass majorant
(`correlationInfinite_pair_product_le_four_div_one_add_pow_pseudoMassFromParamsAtPair`,
PR #3155) yields

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
with `correlationInfinite_pair_product_le_four_div_one_add_pow_pseudoMassFromParamsAtPair`
(PR #3155) applied to each of the two pair-product terms, then `add_le_add` with appropriate
non-negativity. -/
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

end Ambient
end IsingModel
