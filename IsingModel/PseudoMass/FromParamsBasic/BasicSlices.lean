import IsingModel.PseudoMass.Ext

/-!
# Pseudo-mass from parameters: basic slices

Basic bridge definition and trivial slice wrappers for pseudo-mass from physical parameters.
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

end IsingModel
