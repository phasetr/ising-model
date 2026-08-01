import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLiebCore

/-!
# HLS bridge from Simon-Lieb: per-pair / symmetric / translation variants

Variants child module of the build-speed split of `HLSBridgeFromSimonLieb`.
Collects the per-pair, symmetric, mixed-anchor, and translation-invariance
specializations of the core Simon-Lieb HLS sum bridge.  See the umbrella
`HLSBridgeFromSimonLieb` for the full narrative and references.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Variant bundle: per-pair / symmetric / mixed-anchor specializations -/

/-- **HLS sum existential at the diagonal `(x₀, x₀)`**.

Diagonal specialization of
`tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent`
at `y₀ := x₀`, the most common shape for `χ_∞(x₀)^2`-type estimates. -/
theorem tsum_correlationInfinite_pair_product_diagonal_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp x₀ x₀

/-- **HLS sum existential symmetric in `(x₀, y₀)` ↔ `(y₀, x₀)`**.

Symmetric variant under the swap `x₀ ↔ y₀`. Direct consequence of the
non-symmetric form combined with the commutativity of multiplication —
the underlying constant is the same. -/
theorem tsum_correlationInfinite_pair_product_swap_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp y₀ x₀

/-- **Ferromagnetic-unfolded form of `PseudoMassLatticeDistanceBridge`
end-to-end constructor**.

The `Ferromagnetic ⟨J, 0, β⟩` witness `⟨hJ, le_refl 0, hβ⟩` is unfolded
to its explicit components, useful for callers that haven't already
packaged the ferromagnetic predicate. -/
def PseudoMassLatticeDistanceBridge_ferromagnetic_unfolded
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M)) :
    PseudoMassLatticeDistanceBridge hα hr d J β :=
  PseudoMassLatticeDistanceBridge_of_simonLieb_smallReg_adjacent
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp

/-- **Constant K positivity from the existential HLS sum bound**.

Exposes the positive K witness extracted from the existential, useful for
downstream `K > 0`-dependent reasoning. -/
theorem hls_const_pos_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K :=
  let ⟨K, hK_pos, _⟩ :=
    tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
      hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
      h_corr_small h_adj_exp x₀ y₀
  ⟨K, hK_pos⟩

/-- **Active range provider standalone form for the zero anchor**.

Zero-anchored version of `all_pair_active_of_betaJ_pos_provider`. -/
theorem zero_anchor_active_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    ∀ w : Fin d → ℤ, w ≠ 0 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  intro w hw_ne
  exact correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos 0 w
    (fun h => hw_ne h.symm)

/-- **Per-`w` non-vanishing of correlation from active range**.

Lower bound `0 < correlationInfinite {0, w}` for `w ≠ 0` distilled from
the active range. Useful when only the strict positivity is needed (not
the full `Ioo 0 2` membership). -/
theorem correlationInfinite_pos_of_betaJ_pos_zero_anchor
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {w : Fin d → ℤ} (hw_ne : w ≠ 0) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w} :=
  (zero_anchor_active_of_betaJ_pos hβ hβJ_pos w hw_ne).1

/-- **Per-pair non-vanishing of correlation from active range**.

Per-distinct-pair version of
`correlationInfinite_pos_of_betaJ_pos_zero_anchor`. -/
theorem correlationInfinite_pos_of_betaJ_pos_pair
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    0 < Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
  (correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos x z hxz).1

/-- **Per-pair upper bound from active range**.

Upper bound `correlationInfinite {x, z} < 2` distilled from the active
range. (The sharper `≤ 1` follows from
`correlationInfinite_latticeGraph_le_one`.) -/
theorem correlationInfinite_lt_two_of_betaJ_pos_pair
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      < 2 :=
  (correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos x z hxz).2

/-! ## Variant bundle: translation invariance properties -/

/-- **Active range at any translated distinct pair `(x + v, z + v)`**.

Direct application of `correlationInfinite_pair_active_of_betaJ_pos`
to the translated pair `(x + v, z + v)`. The translated pair is also
distinct because addition by `v` is injective. -/
theorem correlationInfinite_pair_active_translation_invariant_of_betaJ_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (v : Fin d → ℤ) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {x + v, z + v}
        ∈ Set.Ioo (0 : ℝ) 2 := by
  intro x z hxz
  have hxv_ne : x + v ≠ z + v := by
    intro h; apply hxz
    have := add_right_cancel h
    exact this
  exact correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos
    (x + v) (z + v) hxv_ne

/-- **`bridge.bound` at the translated distinct pair `(x + v, z + v)`**.

Direct application of `all_pair_bound_of_simonLieb_smallReg_adjacent_provider`
to the translated pair `(x + v, z + v)`. The translated pair is also
distinct because addition by `v` is injective. -/
theorem pseudoMassFromParamsAtPair_all_pair_bound_translation_invariant
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (v : Fin d → ℤ) :
    ∀ x z : Fin d → ℤ, x ≠ z →
      M * (latticeDistance d (x + v) (z + v) : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) (x + v) (z + v) * r := by
  intro x z hxz
  have hxv_ne : x + v ≠ z + v := by
    intro h; apply hxz; exact add_right_cancel h
  exact all_pair_bound_of_simonLieb_smallReg_adjacent_provider
    hα hr d hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp (x + v) (z + v) hxv_ne

/-- **HLS sum bound at translated anchor `(x₀ + v, y₀ + v)`**.

Direct application of the HLS sum existential at the translated anchor. -/
theorem tsum_correlationInfinite_pair_product_translated_anchor_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (x₀ y₀ v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {x₀ + v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
              {y₀ + v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp (x₀ + v) (y₀ + v)

/-- **HLS sum bound at the displacement anchor `(0, v)`**.

Specialization to the displacement-pair anchor `(0, v)`. -/
theorem tsum_correlationInfinite_pair_product_zero_v_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp 0 v

/-- **Lattice-distance displacement identity for the bound shape**.

For distinct `(x, z)`, the bound `M · d(x, z) ≤ pseudoMass · r` rewrites
as `M · d(0, z - x) ≤ pseudoMass · r` using
`latticeDistance_translate_eq`. -/
theorem bound_shape_displacement_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {M : ℝ} (x z : Fin d → ℤ)
    (hbound : M * (latticeDistance d 0 (z - x) : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 (z - x) * r) :
    M * (latticeDistance d x z : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z * r := by
  have h_dist : (latticeDistance d x z : ℝ) =
      (latticeDistance d 0 (z - x) : ℝ) := by
    exact_mod_cast latticeDistance_translate_eq d x z
  have h_pseudo := pseudoMassFromParamsAtPair_eq_displacement hα hr d hJ hβ x z
  rw [h_dist, h_pseudo]
  exact hbound

/-- **Active range transfer from zero-anchor displacement**.

One-way transfer: if active range holds at the zero-anchored displacement
`(0, z - x)`, then it holds at `(x, z)` by translation invariance of the
pair correlation (`correlationInfinite_pair_eq_displacement`). -/
theorem active_displacement_eq
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (x z : Fin d → ℤ)
    (h_active_zero : Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z - x}
        ∈ Set.Ioo (0 : ℝ) 2) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
  exact h_active_zero

/-- **Composite displacement form for bridge.bound**.

Combining `bound_shape_displacement_eq` and `active_displacement_eq`
factors per-pair `bridge.bound` through the zero-anchored displacement. -/
theorem bridge_bound_active_displacement_composite
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {M : ℝ} (x z : Fin d → ℤ)
    (hbound_zero : M * (latticeDistance d 0 (z - x) : ℝ) ≤
      pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) 0 (z - x) * r)
    (h_active_zero : Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, z - x}
        ∈ Set.Ioo (0 : ℝ) 2) :
    (M * (latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hr d (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z * r) ∧
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2 :=
  ⟨bound_shape_displacement_eq hα hr d hJ hβ x z hbound_zero,
   active_displacement_eq hJ hβ x z h_active_zero⟩

/-- **Antipode form: HLS sum at the antipode anchor `(v, -v)`**.

Specialization at the antipode pair anchor `(v, -v)`. -/
theorem tsum_correlationInfinite_pair_product_antipode_le_const_of_simonLieb
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (d : ℕ) (hαd : d < 2 * α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d)) (hβJd_le : β * J * (2 * d) ≤ 1)
    {M : ℝ} (hM_pos : 0 < M)
    (hMrate : M ≤ simonLiebRate β J d / 2)
    (h_corr_small : ∀ w : Fin d → ℤ, w ≠ 0 →
      M * (latticeDistance d 0 w : ℝ) ≤ 1)
    (h_adj_exp : ∀ w : Fin d → ℤ, latticeDistance d 0 w = 1 →
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {0, w}
        ≤ Real.exp (-M))
    (v : Fin d → ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {-v, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp v (-v)

end Ambient
end IsingModel
