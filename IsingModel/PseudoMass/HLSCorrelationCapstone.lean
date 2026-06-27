import IsingModel.PseudoMass.HLSPairBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivialHZero

/-!
# HLS correlation pair-product capstone for GJ §17.5 p. 312 derivative bound

Step 119 plan Step 5.6: capstone bounding the HLS-form sum
`∑_z ⟨φ(x_0)φ(z)⟩ · ⟨φ(y_0)φ(z)⟩` used in GJ §17.5 p. 312 to derive
`|c'| ≤ K · c · m⁻^(-2α)`.

Strategy: abstract the pseudo-mass-to-lattice-distance lower bound
`M_inf · d(x,z) ≤ m⁻·r'` as a `PseudoMassLatticeDistanceBridge` structure, and
use it to derive the sum bound. The bridge's own construction (from cubic-path
exponential decay / Simon-Lieb) is the subject of a separate PR.

The case `z = x_0` (or `z = y_0`) is handled automatically: `{x, x} = {x}`
(Finset insert idempotent) is a singleton, so its h = 0 correlation vanishes
by the odd-cardinality Z₂ symmetry, and the pair product is 0. There is no
need to restrict the sum to `ℤ^d \ {x_0, y_0}`.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311-312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Pseudo-mass to lattice-distance bridge structure** (Step 119 plan Step 5.6).

Abstracts the per-pair pseudo-mass lower bound in terms of lattice distance,
together with the ferromagnetic and active-range assumptions required for the
GJ §17.5 p. 312 HLS step:

- `M_inf > 0`: volume-independent mass lower bound.
- `hf`: the system is ferromagnetic (J ≥ 0, h = 0).
- `bound`: for every distinct pair `x ≠ z`,
  `M_inf · d(x,z) ≤ pseudoMassFromParamsAtPair · r'`.
- `active`: for every distinct pair `x ≠ z`, the associated correlation lies
  in the active range `Ioo 0 2`.

Given such a bridge, the HLS sum bound follows mechanically. The bridge
construction itself (cubic-path exponential decay + `pseudoMassG` comparison)
is left to a subsequent PR. -/
structure PseudoMassLatticeDistanceBridge
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (J β : ℝ) where
  /-- Volume-independent mass lower bound. -/
  M_inf : ℝ
  /-- Positivity of the mass lower bound. -/
  M_inf_pos : 0 < M_inf
  /-- The system is ferromagnetic at `h = 0`. -/
  hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)
  /-- Per-pair pseudo-mass dominates `M_inf · d(x,z)`. -/
  bound : ∀ x z : Fin d → ℤ, x ≠ z →
    M_inf * (latticeDistance d x z : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z * r'
  /-- Per-pair correlation lies in the active range. -/
  active : ∀ x z : Fin d → ℤ, x ≠ z →
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2

/-- **Singleton-pair correlation vanishes at `h = 0`** (helper, Step 5.6).

`{x, x} = {x}` (Finset insert idempotent) is a singleton of cardinality 1
(odd), so the `h = 0` Z₂ symmetry gives
`correlationInfinite ⟨J, 0, β⟩ {x, x} = 0`. -/
theorem correlationInfinite_pair_self_h_zero
    (d : ℕ) (J β : ℝ) (x : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, x} = 0 := by
  have hsing : ({x, x} : Finset (Fin d → ℤ)) = {x} := by ext y; simp
  rw [hsing]
  exact correlationInfinite_latticeGraph_cubicExhaustion_h_zero d J β {x}
    (by simp only [Finset.card_singleton]; exact ⟨0, rfl⟩)

/-- **Pointwise comparison for the HLS correlation pair-product bound**
(helper, Step 5.6).

Uses the bridge to dominate `corr{x₀,z} · corr{y₀,z}` pointwise by
`2/(1+(M·d(x₀,z))^α) · 2/(1+(M·d(y₀,z))^α)`:

- If `z = x₀` or `z = y₀`: the LHS is a product involving a singleton
  correlation that vanishes by `correlationInfinite_pair_self_h_zero`.
- Otherwise: combine Step 5.1 (#3154) with `bridge.bound` and the
  monotonicity of `2/(1+(·)^α)`. -/
theorem correlationInfinite_pair_product_le_pseudoMass_pair
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr' d J β)
    (x₀ y₀ z : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} ≤
      2 / (1 + (bridge.M_inf * (latticeDistance d x₀ z : ℝ)) ^ α) *
        (2 / (1 + (bridge.M_inf * (latticeDistance d y₀ z : ℝ)) ^ α)) := by
  set M := bridge.M_inf with hM_def
  have hM_pos : 0 < M := bridge.M_inf_pos
  -- Positivity of the RHS factors.
  have hRHS_x_pos : 0 < 2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) := by
    apply div_pos (by norm_num)
    have hMt_nn : (0 : ℝ) ≤ M * (latticeDistance d x₀ z : ℝ) := by
      apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
    have h_pow_nn : (0 : ℝ) ≤ (M * (latticeDistance d x₀ z : ℝ)) ^ α := pow_nonneg hMt_nn α
    linarith
  have hRHS_y_pos : 0 < 2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α) := by
    apply div_pos (by norm_num)
    have hMt_nn : (0 : ℝ) ≤ M * (latticeDistance d y₀ z : ℝ) := by
      apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
    have h_pow_nn : (0 : ℝ) ≤ (M * (latticeDistance d y₀ z : ℝ)) ^ α := pow_nonneg hMt_nn α
    linarith
  have hRHS_prod_pos : 0 < 2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
      (2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α)) := mul_pos hRHS_x_pos hRHS_y_pos
  -- Case `z = x₀`: the LHS is 0.
  by_cases hzx : x₀ = z
  · subst hzx
    rw [correlationInfinite_pair_self_h_zero d J β x₀, zero_mul]
    exact hRHS_prod_pos.le
  by_cases hzy : y₀ = z
  · subst hzy
    rw [correlationInfinite_pair_self_h_zero d J β y₀, mul_zero]
    exact hRHS_prod_pos.le
  -- Case `z ∉ {x₀, y₀}`: the substantive bound.
  have h_x_active := bridge.active x₀ z hzx
  have h_y_active := bridge.active y₀ z hzy
  have h_x_step51 :=
    correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
      hα hr' (Ambient.cubicExhaustion d) J β x₀ z h_x_active
  have h_y_step51 :=
    correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
      hα hr' (Ambient.cubicExhaustion d) J β y₀ z h_y_active
  -- `bridge.bound`: `m⁻ · r' ≥ M · d`.
  have h_x_bnd := bridge.bound x₀ z hzx
  have h_y_bnd := bridge.bound y₀ z hzy
  -- Monotonicity: `M·d ≤ m⁻·r'` implies
  -- `2/(1+(m⁻·r')^α) ≤ 2/(1+(M·d)^α)`.
  set m_x := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x₀ z with hm_x_def
  set m_y := pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) y₀ z with hm_y_def
  have hMdx_nn : (0 : ℝ) ≤ M * (latticeDistance d x₀ z : ℝ) := by
    apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
  have hMdy_nn : (0 : ℝ) ≤ M * (latticeDistance d y₀ z : ℝ) := by
    apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
  have hmxr_nn : (0 : ℝ) ≤ m_x * r' := by
    apply mul_nonneg (pseudoMassFromParamsAtPair_nonneg hα hr' d _ _ _ _) hr'.le
  have hmyr_nn : (0 : ℝ) ≤ m_y * r' := by
    apply mul_nonneg (pseudoMassFromParamsAtPair_nonneg hα hr' d _ _ _ _) hr'.le
  have h_x_mono : 2 / (1 + (m_x * r') ^ α) ≤
      2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) := by
    apply div_le_div_of_nonneg_left (by norm_num)
    · have h_pow_nn : (0 : ℝ) ≤ (M * (latticeDistance d x₀ z : ℝ)) ^ α := pow_nonneg hMdx_nn α
      linarith
    · have hpow_le : (M * (latticeDistance d x₀ z : ℝ)) ^ α ≤ (m_x * r') ^ α :=
        pow_le_pow_left₀ hMdx_nn h_x_bnd α
      linarith
  have h_y_mono : 2 / (1 + (m_y * r') ^ α) ≤
      2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α) := by
    apply div_le_div_of_nonneg_left (by norm_num)
    · have h_pow_nn : (0 : ℝ) ≤ (M * (latticeDistance d y₀ z : ℝ)) ^ α := pow_nonneg hMdy_nn α
      linarith
    · have hpow_le : (M * (latticeDistance d y₀ z : ℝ)) ^ α ≤ (m_y * r') ^ α :=
        pow_le_pow_left₀ hMdy_nn h_y_bnd α
      linarith
  -- Sandwich via GKS-I nonnegativity + Step 5.1 + monotonicity.
  have h_x_nn : (0 : ℝ) ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
  have h_y_nn : (0 : ℝ) ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
  -- Chain.
  calc Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ 2 / (1 + (m_x * r') ^ α) * (2 / (1 + (m_y * r') ^ α)) := by
        apply mul_le_mul h_x_step51 h_y_step51 h_y_nn
        positivity
    _ ≤ 2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
          (2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α)) := by
        apply mul_le_mul h_x_mono h_y_mono
        · positivity
        · exact hRHS_x_pos.le

/-- **HLS correlation pair-product tsum capstone** (Step 119 plan Step 5.6).

Given a `PseudoMassLatticeDistanceBridge`, derives the GJ §17.5 p. 312 HLS-form
sum bound:
```
∃ K > 0, ∑_z ⟨φ(x_0)φ(z)⟩ · ⟨φ(y_0)φ(z)⟩ ≤ K
```
where `K > 0` depends only on `M_inf`, `α`, and `d`. Hypotheses: `1 ≤ α`,
`0 < r'`, `d < 2 * α`.

Proof outline:

1. At `z = x_0` (or `z = y_0`), `{x_0, z}` becomes the singleton `{x_0}`;
   the h = 0 odd-cardinality Z₂ symmetry forces the correlation to vanish.
   The pair product is 0.
2. For `z ∉ {x_0, y_0}`, Step 5.1
   (`correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair`)
   bounds each correlation by `2/(1+(m⁻·r')^α)`; `bridge.bound` gives
   `m⁻·r' ≥ M_inf·d`, and monotonicity yields `2/(1+(m⁻·r')^α) ≤
   2/(1+(M_inf·d)^α)`.
3. The pair product is summed via
   `discrete_hls_pseudoMass_two_pair_convolution_constant` (#3170).

Summability of the LHS is established by comparison with an AM-GM bound
reconstructed here, paralleling the proof of
`tsum_pseudoMass_pair_product_le_const_pow_M`.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, p. 312. -/
theorem tsum_correlationInfinite_pair_product_le_HLS_const
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (hαd : d < 2 * α) (J β : ℝ)
    (bridge : PseudoMassLatticeDistanceBridge hα hr' d J β)
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K := by
  set M := bridge.M_inf with hM_def
  have hM_pos : 0 < M := bridge.M_inf_pos
  -- Obtain the comparison constant from #3170.
  obtain ⟨K₀, hK₀_pos, hK₀_bound⟩ :=
    discrete_hls_pseudoMass_two_pair_convolution_constant d α hαd
  set C := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hC_def
  have hC_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (pow_pos (by norm_num) α)
  refine ⟨4 * C ^ 2 * K₀, by positivity, ?_⟩
  -- Define LHS summand `f` and comparison summand `g`.
  set f : (Fin d → ℤ) → ℝ := fun z =>
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      with hf_def
  set g : (Fin d → ℤ) → ℝ := fun z =>
      2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
        (2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α))
      with hg_def
  -- Pointwise comparison.
  have h_pointwise : ∀ z, f z ≤ g z := fun z =>
    correlationInfinite_pair_product_le_pseudoMass_pair hα hr' d J β bridge x₀ y₀ z
  -- Pointwise nonnegativity of `f`.
  have hf_nn : ∀ z, 0 ≤ f z := fun z => by
    change 0 ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
    apply mul_nonneg
    · exact Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
    · exact Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
  -- The sum of `g` is bounded via #3170.
  have h_g_sum_le : ∑' z, g z ≤ 4 * C ^ 2 * K₀ := hK₀_bound hM_pos x₀ y₀
  -- Pointwise nonnegativity of `g` (each factor is positive).
  have hg_nn : ∀ z, 0 ≤ g z := fun z => by
    have hMdx_nn : (0 : ℝ) ≤ M * (latticeDistance d x₀ z : ℝ) := by
      apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
    have hMdy_nn : (0 : ℝ) ≤ M * (latticeDistance d y₀ z : ℝ) := by
      apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
    have h_x_pos : 0 < 2 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) := by
      apply div_pos (by norm_num); have := pow_nonneg hMdx_nn α; linarith
    have h_y_pos : 0 < 2 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α) := by
      apply div_pos (by norm_num); have := pow_nonneg hMdy_nn α; linarith
    exact (mul_pos h_x_pos h_y_pos).le
  -- Summability of `g`, reconstructed via AM-GM (parallel to PolyDecay).
  have hα_real : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  have h_g_summable : Summable g := by
    -- `g = 4 · h`, where `h` is the base #3168 summand.
    set h : (Fin d → ℤ) → ℝ := fun z =>
        1 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
          (1 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α))
        with hh_def
    have h_eq : g = fun z => 4 * h z := by
      funext z
      change _ = 4 * _
      ring
    rw [h_eq]
    apply Summable.mul_left 4
    -- Real-α rpow companion of `h`.
    set h_rpow : (Fin d → ℤ) → ℝ := fun z =>
        (1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
          (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))
        with hh_rpow_def
    -- `h_rpow` summable via AM-GM.
    have h_avg_summable : Summable (fun z =>
        ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-((2 : ℝ) * α)) +
         (1 + (latticeDistance d y₀ z : ℝ)) ^ (-((2 : ℝ) * α))) / 2) := by
      have hSx := summable_pow_neg_translate (γ := (2 : ℝ) * α) d x₀ hα_real
      have hSy := summable_pow_neg_translate (γ := (2 : ℝ) * α) d y₀ hα_real
      exact (hSx.add hSy).div_const 2
    have h_rpow_nn : ∀ z, 0 ≤ h_rpow z := fun z =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
    have h_rpow_le_avg : ∀ z, h_rpow z ≤
        ((1 + (latticeDistance d x₀ z : ℝ)) ^ (-((2 : ℝ) * α)) +
         (1 + (latticeDistance d y₀ z : ℝ)) ^ (-((2 : ℝ) * α))) / 2 := by
      intro z
      set a := (1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ))
      set b := (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))
      have ha2 : a ^ 2 = (1 + (latticeDistance d x₀ z : ℝ)) ^ (-((2 : ℝ) * α)) := by
        simp only [a]
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
        congr 1; ring
      have hb2 : b ^ 2 = (1 + (latticeDistance d y₀ z : ℝ)) ^ (-((2 : ℝ) * α)) := by
        simp only [b]
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
        congr 1; ring
      change a * b ≤ _
      nlinarith [sq_nonneg (a - b), ha2, hb2]
    have h_rpow_summable : Summable h_rpow :=
      Summable.of_nonneg_of_le h_rpow_nn h_rpow_le_avg h_avg_summable
    -- Pointwise `h z ≤ C^2 · h_rpow z` via the pair-pointwise bridge + form bridge.
    have h_h_nn : ∀ z, 0 ≤ h z := fun z => by
      change 0 ≤ 1 / _ * (1 / _)
      have hMdx_nn : (0 : ℝ) ≤ M * (latticeDistance d x₀ z : ℝ) := by
        apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
      have hMdy_nn : (0 : ℝ) ≤ M * (latticeDistance d y₀ z : ℝ) := by
        apply mul_nonneg hM_pos.le; exact_mod_cast Nat.zero_le _
      have h1x : 0 < 1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α := by
        have := pow_nonneg hMdx_nn α; linarith
      have h1y : 0 < 1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α := by
        have := pow_nonneg hMdy_nn α; linarith
      exact mul_nonneg (div_nonneg (by norm_num) h1x.le)
        (div_nonneg (by norm_num) h1y.le)
    have h_h_le : ∀ z, h z ≤ C ^ 2 * h_rpow z := fun z => by
      have hd_x_nn : (0 : ℝ) ≤ (latticeDistance d x₀ z : ℝ) := by
        exact_mod_cast Nat.zero_le _
      have hd_y_nn : (0 : ℝ) ≤ (latticeDistance d y₀ z : ℝ) := by
        exact_mod_cast Nat.zero_le _
      have h_pair :=
        one_div_one_add_M_t_pow_pair_le_const_sq_mul_one_div_one_add_pow_pow
          (M := M) (tx := (latticeDistance d x₀ z : ℝ))
          (ty := (latticeDistance d y₀ z : ℝ)) (α := α) hM_pos hd_x_nn hd_y_nn
      have hdx_eq : 1 / (1 + (latticeDistance d x₀ z : ℝ)) ^ α =
          (1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) :=
        one_div_one_add_pow_eq_rpow_neg hd_x_nn
      have hdy_eq : 1 / (1 + (latticeDistance d y₀ z : ℝ)) ^ α =
          (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ)) :=
        one_div_one_add_pow_eq_rpow_neg hd_y_nn
      change 1 / _ * (1 / _) ≤ _
      have h_pair' :
          1 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
            (1 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α)) ≤
          C ^ 2 *
            (1 / (1 + (latticeDistance d x₀ z : ℝ)) ^ α *
              (1 / (1 + (latticeDistance d y₀ z : ℝ)) ^ α)) := h_pair
      rw [hdx_eq, hdy_eq] at h_pair'
      exact h_pair'
    have h_Crpow_summable : Summable (fun z => C ^ 2 * h_rpow z) :=
      h_rpow_summable.mul_left _
    exact Summable.of_nonneg_of_le h_h_nn h_h_le h_Crpow_summable
  -- `f` summable by comparison with `g`.
  have h_f_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nn h_pointwise h_g_summable
  -- Final chain: `∑ f ≤ ∑ g ≤ 4·C²·K₀`.
  calc ∑' z, f z
      ≤ ∑' z, g z := h_f_summable.tsum_le_tsum h_pointwise h_g_summable
    _ ≤ 4 * C ^ 2 * K₀ := h_g_sum_le

end Ambient
end IsingModel
