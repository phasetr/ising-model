import IsingModel.PseudoMass.HLSPairBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.PseudoMassFromParamsRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivialHZero

/-!
# HLS correlation pair-product capstone for GJ §17.5 p. 312 derivative bound

Step 119 plan Step 5.6: GJ §17.5 p. 312 で `|c'| ≤ K · c · m⁻^(-2α)` 導出に
用いる `∑_z ⟨φ(x_0)φ(z)⟩ · ⟨φ(y_0)φ(z)⟩` HLS 形和を bound する capstone.

実装方針: pseudo-mass と lattice-distance を結ぶ下界 `M_inf · d(x,z) ≤ m⁻·r'`
を `PseudoMassLatticeDistanceBridge` 構造体で抽象化し, それを用いて
sum bound を導出. bridge の具体構成 (cubic-path / Simon-Lieb 由来)
は別 PR の課題.

`{x, x} = {x}` (Finset insert idempotent) であり, h = 0 ferromagnetic
では cardinality 1 (odd) の correlation は Z₂ symmetry で 0 になるため,
`z = x_0` や `z = y_0` の項は自動的に 0 となり, sum の定義域を
`ℤ^d \ {x_0, y_0}` に制限する必要はない.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311-312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **pseudo-mass ↔ lattice-distance bridge 構造体** (Step 119 plan Step 5.6).

GJ §17.5 p. 312 の HLS step で必要な「per-pair pseudo-mass の下界が lattice
distance に比例する」事実を抽象化:

- `M_inf > 0`: volume-independent な質量定数下界.
- `hf`: 系が ferromagnetic (h = 0, J ≥ 0).
- `bound`: 任意の異なる `x, z` で `M_inf · d(x,z) ≤ pseudoMassFromParamsAtPair · r'`.
- `active`: 任意の異なる `x, z` で対応する correlation が active range `Ioo 0 2`.

この bridge を仮定として受ければ, capstone HLS sum bound が機械的に得られる.
bridge 自体の具体構成は cubic-path exponential decay + pseudoMassG comparison
の合成で別 PR の課題. -/
structure PseudoMassLatticeDistanceBridge
    {α : ℕ} (hα : 1 ≤ α) {r' : ℝ} (hr' : 0 < r')
    (d : ℕ) (J β : ℝ) where
  /-- ボリューム独立な質量定数下界. -/
  M_inf : ℝ
  /-- 質量下界の正値性. -/
  M_inf_pos : 0 < M_inf
  /-- 系が ferromagnetic. -/
  hf : IsingModel.Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ)
  /-- per-pair pseudo-mass が `M_inf · d(x,z)` 以上であることを保証. -/
  bound : ∀ x z : Fin d → ℤ, x ≠ z →
    M_inf * (latticeDistance d x z : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr' d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z * r'
  /-- correlation が active range に入っていることを保証. -/
  active : ∀ x z : Fin d → ℤ, x ≠ z →
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2

/-- **Singleton correlation at h = 0 vanishes** (helper, Step 5.6).

`{x, x} = {x}` (Finset insert idempotent) かつ `{x}` は cardinality 1 (odd),
よって h = 0 の Z₂ symmetry で `correlationInfinite ⟨J, 0, β⟩ {x, x} = 0`. -/
private theorem correlationInfinite_pair_self_h_zero
    (d : ℕ) (J β : ℝ) (x : Fin d → ℤ) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, x} = 0 := by
  have hsing : ({x, x} : Finset (Fin d → ℤ)) = {x} := by ext y; simp
  rw [hsing]
  exact correlationInfinite_latticeGraph_cubicExhaustion_h_zero d J β {x}
    (by simp only [Finset.card_singleton]; exact ⟨0, rfl⟩)

/-- **Pointwise comparison for the HLS correlation pair-product bound**
(helper, Step 5.6).

bridge を用いて per-`z` で `corr{x₀,z} · corr{y₀,z}` を
`2/(1+(M·d(x₀,z))^α) · 2/(1+(M·d(y₀,z))^α)` で押さえる.

- `z = x₀` または `z = y₀` の場合: 左辺は singleton correlation の積で 0.
- それ以外: Step 5.1 (#3154) + `bridge.bound` + 単調性. -/
private theorem correlationInfinite_pair_product_le_pseudoMass_pair
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
  -- RHS の各因子の正値性.
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
  -- z = x₀ の場合: 左辺は 0.
  by_cases hzx : x₀ = z
  · subst hzx
    rw [correlationInfinite_pair_self_h_zero d J β x₀, zero_mul]
    exact hRHS_prod_pos.le
  by_cases hzy : y₀ = z
  · subst hzy
    rw [correlationInfinite_pair_self_h_zero d J β y₀, mul_zero]
    exact hRHS_prod_pos.le
  -- z ≠ x₀ ∧ z ≠ y₀: 通常の bound.
  have h_x_active := bridge.active x₀ z hzx
  have h_y_active := bridge.active y₀ z hzy
  have h_x_step51 :=
    correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
      hα hr' (Ambient.cubicExhaustion d) J β x₀ z h_x_active
  have h_y_step51 :=
    correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair
      hα hr' (Ambient.cubicExhaustion d) J β y₀ z h_y_active
  -- bridge.bound: m⁻ · r' ≥ M · d.
  have h_x_bnd := bridge.bound x₀ z hzx
  have h_y_bnd := bridge.bound y₀ z hzy
  -- 単調性: M·d ≤ m⁻·r' → (M·d)^α ≤ (m⁻·r')^α → 1+(M·d)^α ≤ 1+(m⁻·r')^α
  --       → 2/(1+(m⁻·r')^α) ≤ 2/(1+(M·d)^α).
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
  -- 非負性 (ferromagnetic) と Step 5.1 + 単調性で sandwich.
  have h_x_nn : (0 : ℝ) ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
  have h_y_nn : (0 : ℝ) ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} :=
    Ambient.correlationInfinite_nonneg (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) bridge.hf _
  -- 連鎖.
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

bridge を仮定として受け, GJ p. 312 の HLS 形 sum bound を導出:
```
∑_z ⟨φ(x_0)φ(z)⟩ · ⟨φ(y_0)φ(z)⟩ ≤ K
```
ここで `K > 0` は `M_inf`, `α`, `d` のみに依存する定数.

証明骨格:
1. `z = x_0` または `z = y_0` の場合: `{x_0, z}` が singleton となり,
   h = 0 odd cardinality correlation は Z₂ symmetry で 0. 積は 0.
2. それ以外: Step 5.1 (`correlationInfinite_le_two_div_one_add_pow_pseudoMassFromParamsAtPair`)
   で各 correlation を `2/(1+(m⁻·r')^α)` で bound. `bridge.bound` で
   `m⁻·r' ≥ M_inf·d`, よって `2/(1+(m⁻·r')^α) ≤ 2/(1+(M_inf·d)^α)`.
3. pair-product を `discrete_hls_pseudoMass_two_pair_convolution_constant`
   (#3170) で sum bound.

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
  -- #3170 で comparison constant を取得.
  obtain ⟨K₀, hK₀_pos, hK₀_bound⟩ :=
    discrete_hls_pseudoMass_two_pair_convolution_constant d α hαd
  set C := max 1 (M ^ α)⁻¹ * (2 : ℝ) ^ α with hC_def
  have hC_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (pow_pos (by norm_num) α)
  refine ⟨4 * C ^ 2 * K₀, by positivity, ?_⟩
  -- f, g の定義.
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
  -- pointwise: f z ≤ g z.
  have h_pointwise : ∀ z, f z ≤ g z := fun z =>
    correlationInfinite_pair_product_le_pseudoMass_pair hα hr' d J β bridge x₀ y₀ z
  -- pointwise nonneg of f.
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
  -- #3170 適用で g の sum を bound.
  have h_g_sum_le : ∑' z, g z ≤ 4 * C ^ 2 * K₀ := hK₀_bound hM_pos x₀ y₀
  -- g は summable: 上界 (4·C²·K₀) で bounded above and nonneg.
  -- もっと簡明には: #3170 の中身 `tsum_two_div_pseudoMass_pair_product_le_const_pow_M`
  -- が summability 構築を含む (Summable.of_nonneg_of_le 経由).
  -- ここでは f を bound するために g の summability が要る.
  -- 直接 f の summability + tsum_le を提示するためには g summable が必要.
  -- HLSPairBound 側で g の summability が確立されている (tsum 計算内部で).
  -- 簡略化: f z ≤ g z かつ g z ≥ 0 (positivity).
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
  -- g summable from existing HLS infrastructure.
  -- We reconstruct it using AM-GM (same as PolyDecay).
  have hα_real : (d : ℝ) < 2 * (α : ℝ) := by exact_mod_cast hαd
  have h_g_summable : Summable g := by
    -- g z = 4 · 1/(1+(M·d_x)^α) · 1/(1+(M·d_y)^α). Use tsum_pseudoMass... summability.
    -- 既存 #3168 の証明内で g (1/...·1/...) の summability が証明されている.
    -- 直接利用するため, h_g_sum_le を hg_nn と組み合わせれば良い.
    -- しかし `tsum_le_tsum` には summability が要るので, 構築する.
    -- Strategy: bound g z ≤ K_pointwise · ((1+d_x)^(-2α) + (1+d_y)^(-2α))/2 (AM-GM).
    -- ここで K_pointwise = 4 · C^2 (定数).
    -- (1+d_x)^(-2α) は summable.
    -- これは結局, #3170 内部の summability 構築をやり直すことになる.
    -- もっと簡明な path: g = 4 · h, where h is the base #3168 summand.
    -- h summable は #3168 の証明内部で確立.
    -- ここでは仕方なく再構築する.
    -- Define h := 1/(1+(M·d_x)^α) · 1/(1+(M·d_y)^α).
    set h : (Fin d → ℤ) → ℝ := fun z =>
        1 / (1 + (M * (latticeDistance d x₀ z : ℝ)) ^ α) *
          (1 / (1 + (M * (latticeDistance d y₀ z : ℝ)) ^ α))
        with hh_def
    have h_eq : g = fun z => 4 * h z := by
      funext z
      show _ = 4 * _
      ring
    rw [h_eq]
    -- Summable (4 · h) ↔ Summable h.
    apply Summable.mul_left 4
    -- Now show Summable h. Use AM-GM bridge to (1+d)^(-2α).
    -- Following the same pattern as in tsum_pseudoMass_pair_product_le_const_pow_M.
    set h_rpow : (Fin d → ℤ) → ℝ := fun z =>
        (1 + (latticeDistance d x₀ z : ℝ)) ^ (-(α : ℝ)) *
          (1 + (latticeDistance d y₀ z : ℝ)) ^ (-(α : ℝ))
        with hh_rpow_def
    -- h_rpow summable via AM-GM.
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
    -- h z = ... ≤ C^2 · h_rpow z (from pair pointwise bridge + form bridge).
    -- このため #3168 を per-z 適用. しかし bridges は z ごとに必要.
    -- 直接 pointwise inequality を inline で構築.
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
  -- f summable from comparison.
  have h_f_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nn h_pointwise h_g_summable
  -- ∑ f ≤ ∑ g ≤ 4 · C² · K₀.
  calc ∑' z, f z
      ≤ ∑' z, g z := h_f_summable.tsum_le_tsum h_pointwise h_g_summable
    _ ≤ 4 * C ^ 2 * K₀ := h_g_sum_le

end Ambient
end IsingModel
