import IsingModel.PseudoMass.Composition

/-!
# Pseudo-Mass From Parameters

This module is part of the split `IsingModel.PseudoMass` development.
-/

namespace IsingModel

open Set Real Filter

/-! ## Step 117k: concrete `pseudoMassFromParamsAtPair` (Issue #1645)

Bridges the abstract `pseudoMassExt : ℝ → ℝ` to the concrete physical
parameters `(d, Λ, p, x, z)` by composing with the infinite-volume
correlation function `correlationInfinite (latticeGraph d) Λ p {x, z}`. -/

/-- **Step 117k (Issue #1645): concrete pseudo-mass from physical
parameters and a pair**.

`pseudoMassFromParamsAtPair α hα r hr d Λ p x z` is the pseudo-mass
associated to the infinite-volume correlation
`⟨σ_x σ_z⟩^∞ = correlationInfinite (latticeGraph d) Λ p {x, z}`,
returning `pseudoMass hα hr hc` if this correlation lies in `Ioo 0 2`,
else 0.

This bridges the abstract `pseudoMass : ℝ` (parameterized by `α, r, c`)
to the concrete `latticeMass : (d, Λ, p) → ENNReal` defined in
`Concrete/LatticeGraphCorrelation/Inequalities.lean` via the
correlation at a chosen pair.

For the §17.5 Lemma 17.5.2 application, the natural choice is `r = 1`
and `α` such that `2α > d` (HLS condition); see `lemma_17_5_2_constant_exists`.

**References**: Glimm–Jaffe §17.5, p. 311. -/
noncomputable def pseudoMassFromParamsAtPair {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) : ℝ :=
  pseudoMassExt hα hr
    (Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})

/-- **`pseudoMassFromParamsAtPair` is non-negative**. -/
theorem pseudoMassFromParamsAtPair_nonneg {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z :=
  pseudoMassExt_nonneg hα hr _

/-- **`pseudoMassFromParamsAtPair` positive when the correlation
lies in `Ioo 0 2`**. -/
theorem pseudoMassFromParamsAtPair_pos_of_corr_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hc : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
            ∈ Set.Ioo (0 : ℝ) 2) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z :=
  pseudoMassExt_pos_of_mem hα hr hc

/-- **`pseudoMassFromParamsAtPair` is zero when the correlation falls
outside `Ioo 0 2`**. -/
theorem pseudoMassFromParamsAtPair_eq_zero_of_corr_not_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    (hc : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
            ∉ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 :=
  pseudoMassExt_of_not_mem hα hr hc

/-- **`pseudoMassFromParamsAtPair` at `β = 0` (infinite-temperature
trivial slice)**: equals 0 because the correlation vanishes. -/
theorem pseudoMassFromParamsAtPair_beta_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J h : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, h, 0⟩ : IsingParams ℝ) x z = 0 := by
  have hxz_ne : ({x, z} : Finset (Fin d → ℤ)).Nonempty :=
    ⟨x, by simp⟩
  have hcorr := Ambient.correlationInfinite_beta_zero_vanish
    (IsingModel.latticeGraph d) Λ J h {x, z} hxz_ne
  unfold pseudoMassFromParamsAtPair
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` at `J = 0, h = 0` (trivial-coupling
slice)**: equals 0 because the correlation `tanh(β·0)^2 = 0`.

Direct corollary of `correlationInfinite_J_zero` with `h = 0`. -/
theorem pseudoMassFromParamsAtPair_J_zero_h_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  have hcorr := Ambient.correlationInfinite_J_zero
    (IsingModel.latticeGraph d) Λ 0 β hf {x, z}
  unfold pseudoMassFromParamsAtPair
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  -- correlation = tanh(β·0)^A.card = 0^|{x,z}| = 0
  have htanh : Real.tanh (β * 0) ^ ({x, z} : Finset (Fin d → ℤ)).card = 0 := by
    rw [mul_zero, Real.tanh_zero, zero_pow]
    exact (Finset.Nonempty.card_pos ⟨x, by simp⟩).ne'
  rw [htanh] at hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` is symmetric in `(x, z)`**: the pair
`{x, z}` as a `Finset` is unchanged under swap, hence the correlation
and the resulting pseudo-mass are unchanged. -/
theorem pseudoMassFromParamsAtPair_symm {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassFromParamsAtPair hα hr d Λ p z x := by
  unfold pseudoMassFromParamsAtPair
  congr 2
  exact Finset.pair_comm x z

/-- **`pseudoMassFromParamsAtPair` at `x = z` (degenerate pair) at h = 0**:
`{x, x} = {x}` is a singleton (odd cardinality), and at h = 0 the Z₂
symmetry forces the singleton correlation = magnetization to vanish.
Hence `pseudoMassFromParamsAtPair = 0`. -/
theorem pseudoMassFromParamsAtPair_diag_h_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x x = 0 := by
  unfold pseudoMassFromParamsAtPair
  have hsing : ({x, x} : Finset (Fin d → ℤ)) = {x} := by
    ext y; simp
  rw [hsing]
  have hodd : Odd (({x} : Finset (Fin d → ℤ)).card) := by
    simp only [Finset.card_singleton]
    exact ⟨0, rfl⟩
  have hcorr := Ambient.correlationInfinite_h_zero
    (IsingModel.latticeGraph d) Λ J β {x} hodd
  rw [hcorr]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair` is positive at `J = 0, h > 0, β > 0`
for distinct sites**: the correlation equals `tanh(β·h)^2 ∈ (0, 1) ⊂ Ioo 0 2`,
hence `pseudoMassFromParamsAtPair > 0`. -/
theorem pseudoMassFromParamsAtPair_pos_at_J_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z := by
  apply pseudoMassFromParamsAtPair_pos_of_corr_mem
  -- correlation = tanh(β·h)^|{x, z}| = tanh(β·h)^2
  have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) := ⟨le_refl 0, hh.le, hβ⟩
  have hcorr := Ambient.correlationInfinite_J_zero
    (IsingModel.latticeGraph d) Λ h β hf {x, z}
  rw [hcorr]
  -- |{x, z}| = 2 since x ≠ z
  have hcard : ({x, z} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair hxz]
  rw [hcard]
  refine ⟨?_, ?_⟩
  · -- 0 < tanh(βh)^2
    have htanh_pos : 0 < Real.tanh (β * h) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh)) (Real.cosh_pos _)
    positivity
  · -- tanh(βh)^2 < 2: tanh ∈ (-1, 1) so tanh^2 < 1 < 2
    have htanh_abs : |Real.tanh (β * h)| < 1 := Real.abs_tanh_lt_one _
    have hsq_lt : Real.tanh (β * h) ^ 2 < 1 := by
      have h1 : -1 < Real.tanh (β * h) := neg_lt_of_abs_lt htanh_abs
      have h2 : Real.tanh (β * h) < 1 := lt_of_abs_lt htanh_abs
      nlinarith
    linarith

/-- **`pseudoMassFromParamsAtPair` at `J = 0` explicit form**: equals
`pseudoMass` evaluated at `tanh(βh)^|{x,z}|`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^
                            ({x, z} : Finset (Fin d → ℤ)).card) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf {x, z}]

/-- **`pseudoMassFromParamsAtPair_at_J_zero_eq` distinct form**:
under `x ≠ z`, the cardinality is 2, giving an explicit `tanh^2`. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr (Real.tanh (β * h) ^ 2) := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_eq hα hr d Λ hf x z, Finset.card_pair hxz]

/-- **`pseudoMassFromParamsAtPair` at `h = 0` equals
`pseudoMassExt(truncated2Infinite)`**: at zero external field, the
unconnected pair correlation `⟨σ_x σ_z⟩` agrees with the truncated
2-point Ursell function `⟨σ_x σ_z⟩ - ⟨σ_x⟩⟨σ_z⟩`, since the spin-flip
symmetry forces `⟨σ_x⟩ = ⟨σ_z⟩ = 0`. Thus

  `pseudoMassFromParamsAtPair hα hr d Λ ⟨J, 0, β⟩ x z =
   pseudoMassExt hα hr (truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ x z)`.

This is the bridge identity needed to compare `pseudoMassFromParamsAtPair`
to `latticeMass`, which is defined as the supremum of validating
exponential decay rates of `truncated2Infinite`. (Step 117l support,
Issue #1645.) -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMassExt hα hr
        (Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  unfold pseudoMassFromParamsAtPair
  rw [Ambient.truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β x z]

/-- **At `J = 0` distinct pair, ferromagnetic, `0 < pseudoMassFromParamsAtPair`
iff `0 < h`**: under `Ferromagnetic ⟨0, h, β⟩` (which gives `0 ≤ h`, `0 < β`)
and `x ≠ z`, `0 < pseudoMassFromParamsAtPair ↔ 0 < h`. The forward
direction follows from `_at_J_zero_distinct_eq` + `pseudoMassExt_pos_iff`
(forces `tanh(β·h)^2 ∈ Ioo 0 2`, hence `tanh(β·h) ≠ 0`, hence `β·h ≠ 0`,
combined with `β > 0` gives `h ≠ 0`, then `h > 0` from `h ≥ 0`).
The reverse is `pseudoMassFromParamsAtPair_pos_at_J_zero` (already
proven). -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z ↔ 0 < h := by
  refine ⟨?_, fun hh => pseudoMassFromParamsAtPair_pos_at_J_zero hα hr d Λ hh hf.hβ hxz⟩
  intro hpos
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf hxz] at hpos
  rw [pseudoMassExt_pos_iff hα hr] at hpos
  have htanh_sq_pos : 0 < Real.tanh (β * h) ^ 2 := hpos.1
  have htanh_ne : Real.tanh (β * h) ≠ 0 := by
    intro habs
    rw [habs] at htanh_sq_pos
    norm_num at htanh_sq_pos
  have hβh_ne : β * h ≠ 0 := by
    intro habs
    rw [habs, Real.tanh_zero] at htanh_ne
    exact htanh_ne rfl
  have hh_ne : h ≠ 0 := by
    intro h_eq
    rw [h_eq, mul_zero] at hβh_ne
    exact hβh_ne rfl
  exact lt_of_le_of_ne hf.hh (Ne.symm hh_ne)

/-- **At `J = 0` distinct pair, ferromagnetic, `pseudoMassFromParamsAtPair = 0`
iff `h = 0`**: contrapositive of `_at_J_zero_distinct_pos_iff_h_pos`,
using non-negativity to flip the strict iff. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_distinct_eq_zero_iff_h_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h β : ℝ} (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) x z = 0 ↔ h = 0 := by
  have hh_nonneg : 0 ≤ h := hf.hh
  have hpm_nonneg := pseudoMassFromParamsAtPair_nonneg hα hr d Λ
                        (⟨0, h, β⟩ : IsingParams ℝ) x z
  constructor
  · intro h_eq
    by_contra h_ne
    have hh_pos : 0 < h := lt_of_le_of_ne hh_nonneg (Ne.symm h_ne)
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mpr hh_pos
    linarith
  · intro hh_eq
    by_contra h_pm_ne
    have hpm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨0, h, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have hh_pos : 0 < h :=
      (pseudoMassFromParamsAtPair_at_J_zero_distinct_pos_iff_h_pos
        hα hr d Λ hf hxz).mp hpm_pos
    linarith

/-- **At `J = 0` for distinct pair, `pseudoMassFromParamsAtPair` depends
only on the product `β·h`**: for any two ferromagnetic params
`⟨0, h₁, β₁⟩` and `⟨0, h₂, β₂⟩` with `β₁·h₁ = β₂·h₂`, the bridge values
agree. Direct corollary of `pseudoMassFromParamsAtPair_at_J_zero_distinct_eq`
which gives `pseudoMassExt(tanh(β·h)^2)` — only the product enters
the right-hand side. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_eq_of_product_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h₁ β₁ h₂ β₂ : ℝ}
    (hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β₁⟩ : IsingParams ℝ))
    (hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β₂⟩ : IsingParams ℝ))
    (hprod : β₁ * h₁ = β₂ * h₂)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β₁⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β₂⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz,
      hprod]

/-- **`pseudoMassFromParamsAtPair` strictly anti in `h` at `J = 0`** for
distinct pair, β > 0, h > 0: `tanh(β·h)^2` increases (in `Ioo 0 1 ⊂ Ioo 0 2`)
as h increases (β > 0 fixed), and `pseudoMassExt` is strictly antitone
on `Ioo 0 2`. Companion to `_strictAntiOn_beta_at_J_zero` (β-direction
analogue, PR #1668). -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_h_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun h =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro h₁ hh₁ h₂ hh₂ hlt
  simp only [Set.mem_Ioi] at hh₁ hh₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h₁, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₁.le, hβ⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h₂, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh₂.le, hβ⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₂, β⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h₁, β⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β * h₁) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₁)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β * h₂) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hh₂)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β * h₁) < Real.tanh (β * h₂) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_left hlt hβ)
  have hsq_lt : Real.tanh (β * h₁) ^ 2 < Real.tanh (β * h₂) ^ 2 := by
    have h1 : Real.tanh (β * h₁) ^ 2 = Real.tanh (β * h₁) * Real.tanh (β * h₁) := sq _
    have h2 : Real.tanh (β * h₂) ^ 2 = Real.tanh (β * h₂) * Real.tanh (β * h₂) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β * h₁) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₁)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₁) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₁) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β * h₂) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β * h₂)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β * h₂) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β * h₂) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassFromParamsAtPair` at `J = 0, h = 0` distinct pair = 0**:
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` with
`Ambient.truncated2Infinite_J_zero_of_ne` (which gives 0 for distinct
pair under ferromagnetic, J = 0). Direct corollary at the `J = h = 0`
trivial slice. -/
theorem pseudoMassFromParamsAtPair_at_J_zero_h_zero_eq_zero {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨0, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ 0 β x z]
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  rw [Ambient.truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ 0 β hf hxz]
  apply pseudoMassExt_of_not_mem
  intro hmem
  exact lt_irrefl 0 hmem.1

/-- **`pseudoMassFromParamsAtPair > 0 at `h = 0` ↔ `0 < truncated2Infinite`**:
under ferromagnetic params, since `truncated2Infinite ∈ [0, 1] ⊂ [0, 2)`
(`truncated2Infinite_nonneg` + `truncated2Infinite_le_one`), the
`Ioo 0 2` membership of truncated2 is equivalent to strict positivity.
Combined with `pseudoMassFromParamsAtPair_at_h_zero_eq` and
`pseudoMassExt_pos_iff` to give the iff in terms of truncated2. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  rw [pseudoMassExt_pos_iff hα hr]
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ 1 :=
    Ambient.truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  refine ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩

/-- **`pseudoMassFromParamsAtPair = 0 at `h = 0` ↔ `truncated2Infinite = 0`**:
contrapositive form of `_at_h_zero_pos_iff` under non-negativity of
truncated2 (which holds in the ferromagnetic regime). -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z = 0 := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnonneg : 0 ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                        (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf x z
  have hpm_nonneg : 0 ≤ pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    pseudoMassFromParamsAtPair_nonneg hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z
  constructor
  · intro hzero
    by_contra h_t_ne
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hnonneg (Ne.symm h_t_ne)
    have hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mpr h_t_pos
    linarith
  · intro hzero
    by_contra h_pm_ne
    have h_pm_pos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      lt_of_le_of_ne hpm_nonneg (Ne.symm h_pm_ne)
    have h_t_pos : 0 < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
      (pseudoMassFromParamsAtPair_at_h_zero_pos_iff hα hr d Λ hJ hβ x z).mp h_pm_pos
    linarith

/-- **`pseudoMassFromParamsAtPair` upper-bounded by `pseudoMass` at a
positive correlation lower bound**: if `c_min ≤ correlationInfinite ...`
with `c_min ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassFromParamsAtPair
≤ pseudoMass(c_min)`. (Requires correlation also in `Ioo 0 2`.) -/
theorem pseudoMassFromParamsAtPair_le_of_corr_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_min
  · rw [heq]
  · have hlt : c_min <
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
      lt_of_le_of_ne hge (Ne.symm heq)
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hc_min hcorr hlt)

/-- **`pseudoMassFromParamsAtPair` lower-bounded by `pseudoMass` at a
correlation upper bound**: if `correlationInfinite ... ≤ c_max` with
`c_max ∈ Ioo 0 2`, then by anti-monotonicity, `pseudoMassExt c_max ≤
pseudoMassFromParamsAtPair`. -/
theorem pseudoMassFromParamsAtPair_ge_of_corr_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z := by
  unfold pseudoMassFromParamsAtPair
  by_cases heq :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} = c_max
  · rw [heq]
  · have hlt :
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} <
          c_max := lt_of_le_of_ne hle heq
    exact le_of_lt
      (pseudoMassExt_strictAntiOn hα hr hcorr hc_max hlt)

/-- **`pseudoMassFromParamsAtPair` strictly anti in β at `J = 0`** for
distinct pair, `h > 0`, β > 0: as β increases, `tanh(βh)^2` increases
(remaining in `Ioo 0 1 ⊂ Ioo 0 2`), and `pseudoMass` is strictly
antitone in its correlation argument. -/
theorem pseudoMassFromParamsAtPair_strictAntiOn_beta_at_J_zero
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 < h) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    StrictAntiOn (fun β =>
        pseudoMassFromParamsAtPair hα hr d Λ
          (⟨0, h, β⟩ : IsingParams ℝ) x z) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hlt
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  have hf₁ : Ferromagnetic (⟨(0 : ℝ), h, β₁⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₁⟩
  have hf₂ : Ferromagnetic (⟨(0 : ℝ), h, β₂⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, hh.le, hβ₂⟩
  change pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₂⟩ : IsingParams ℝ) x z
        < pseudoMassFromParamsAtPair hα hr d Λ (⟨0, h, β₁⟩ : IsingParams ℝ) x z
  rw [pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₁ hxz,
      pseudoMassFromParamsAtPair_at_J_zero_distinct_eq hα hr d Λ hf₂ hxz]
  have htanh_pos₁ : 0 < Real.tanh (β₁ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₁ hh)) (Real.cosh_pos _)
  have htanh_pos₂ : 0 < Real.tanh (β₂ * h) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ₂ hh)) (Real.cosh_pos _)
  have htanh_mono : Real.tanh (β₁ * h) < Real.tanh (β₂ * h) :=
    Real.tanh_strictMono (mul_lt_mul_of_pos_right hlt hh)
  have hsq_lt : Real.tanh (β₁ * h) ^ 2 < Real.tanh (β₂ * h) ^ 2 := by
    have h1 : Real.tanh (β₁ * h) ^ 2 = Real.tanh (β₁ * h) * Real.tanh (β₁ * h) := sq _
    have h2 : Real.tanh (β₂ * h) ^ 2 = Real.tanh (β₂ * h) * Real.tanh (β₂ * h) := sq _
    rw [h1, h2]
    exact mul_lt_mul' htanh_mono.le htanh_mono htanh_pos₁.le htanh_pos₂
  have hmem₁ : Real.tanh (β₁ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₁ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₁ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₁ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  have hmem₂ : Real.tanh (β₂ * h) ^ 2 ∈ Set.Ioo (0 : ℝ) 2 := by
    refine ⟨by positivity, ?_⟩
    have habs : |Real.tanh (β₂ * h)| < 1 := Real.abs_tanh_lt_one _
    have h1 : -1 < Real.tanh (β₂ * h) := neg_lt_of_abs_lt habs
    have h2 : Real.tanh (β₂ * h) < 1 := lt_of_abs_lt habs
    nlinarith
  exact pseudoMassExt_strictAntiOn hα hr hmem₁ hmem₂ hsq_lt

/-- **`pseudoMassFromParamsAtPair` independence of exhaustion for
ferromagnetic params**: `correlationInfinite` is exhaustion-independent
under ferromagnetic hypothesis, hence so is the bridge. -/
theorem pseudoMassFromParamsAtPair_indep_exhaustion {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z =
      pseudoMassFromParamsAtPair hα hr d Λ' p x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  exact Ambient.correlationInfinite_indep_exhaustion
    (IsingModel.latticeGraph d) Λ Λ' p hf {x, z}

/-- **`pseudoMassFromParamsAtPair` h-symmetry under `h → -h` for distinct
pairs**: `|{x, z}| = 2` is even, so `correlationInfinite` is unchanged
under `h ↦ -h`, hence the bridge is too. -/
theorem pseudoMassFromParamsAtPair_neg_h_distinct {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J h β : ℝ) {x z : Fin d → ℤ} (hxz : x ≠ z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, -h, β⟩ : IsingParams ℝ) x z =
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, h, β⟩ : IsingParams ℝ) x z := by
  unfold pseudoMassFromParamsAtPair
  congr 1
  have heven : Even (({x, z} : Finset (Fin d → ℤ)).card) := by
    rw [Finset.card_pair hxz]
    decide
  exact Ambient.correlationInfinite_neg_h_of_even_card
    (IsingModel.latticeGraph d) Λ J h β {x, z} heven

/-- **`pseudoMassFromParamsAtPair = 0 ↔ correlation ∉ Ioo 0 2`**: lifted from
`pseudoMassExt_eq_zero_iff`. -/
theorem pseudoMassFromParamsAtPair_eq_zero_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPair hα hr d Λ p x z = 0 ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∉ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_eq_zero_iff hα hr _

/-- **`pseudoMassFromParamsAtPair > 0 ↔ correlation ∈ Ioo 0 2`**: lifted from
`pseudoMassExt_pos_iff`. -/
theorem pseudoMassFromParamsAtPair_pos_iff {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ p x z ↔
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  unfold pseudoMassFromParamsAtPair
  exact pseudoMassExt_pos_iff hα hr _

/-- **`pseudoMassFromParamsAtPair` sandwich**: if `c_min ≤ correlation ≤ c_max`
all in `Ioo 0 2`, then `pseudoMassExt c_max ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt c_min`.

This packages `_le_of_corr_ge` and `_ge_of_corr_le` into a single sandwich
inequality, useful for the §17.5 Lemma 17.5.2 capstone. -/
theorem pseudoMassFromParamsAtPair_sandwich_of_corr_mem {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z})
    (hle : Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
              ≤ c_max) :
    pseudoMassExt hα hr c_max ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ p x z ≤ pseudoMassExt hα hr c_min :=
  ⟨pseudoMassFromParamsAtPair_ge_of_corr_le hα hr d Λ p x z hc_max hcorr hle,
   pseudoMassFromParamsAtPair_le_of_corr_ge hα hr d Λ p x z hc_min hcorr hge⟩


end IsingModel
