import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagAlongExConvergenceCiSup

/-!
# HLS bridge per-stage / Λ-layer wrappers

GJ-proposition-unit bundled wrappers extending the infinite-volume HLS
bridge constructors (#3188/#3189/#3190) to the per-stage (finite-volume
`correlationAlongExhaustion`) layer, using the existing pointwise comparison
`correlationAlongExhaustion ≤ correlationInfinite` and ferromagnetic
nonnegativity.

**Reference:** Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-! ## Per-stage pointwise comparison wrappers -/

/-- **Per-stage pair correlation pointwise bound** at any stage `n`. -/
theorem correlationAlongExhaustion_pair_le_correlationInfinite_pair
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (x z : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
  correlationAlongExhaustion_le_correlationInfinite_latticeGraph d Λ p {x, z} n

/-- **Per-stage pair correlation nonnegativity** (ferromagnetic). -/
theorem correlationAlongExhaustion_pair_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (x z : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x, z} n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf {x, z} n

/-- **Per-stage pair-product pointwise bound** at any stage `n`. -/
theorem correlationAlongExhaustion_pair_product_le_correlationInfinite_pair_product
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (x₀ y₀ z : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x₀, z} n *
        correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {y₀, z} n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x₀, z} *
        correlationInfinite (IsingModel.latticeGraph d) Λ p {y₀, z} := by
  have hxz_nn :=
    correlationAlongExhaustion_pair_nonneg d Λ p hf x₀ z n
  have hyz_nn :=
    correlationAlongExhaustion_pair_nonneg d Λ p hf y₀ z n
  have h_inf_yz_nn :=
    correlationInfinite_latticeGraph_nonneg d Λ p hf {y₀, z}
  have hxz_le :=
    correlationAlongExhaustion_pair_le_correlationInfinite_pair d Λ p x₀ z n
  have hyz_le :=
    correlationAlongExhaustion_pair_le_correlationInfinite_pair d Λ p y₀ z n
  calc correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x₀, z} n *
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {y₀, z} n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x₀, z} *
          correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {y₀, z} n :=
        mul_le_mul_of_nonneg_right hxz_le hyz_nn
    _ ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x₀, z} *
          correlationInfinite (IsingModel.latticeGraph d) Λ p {y₀, z} := by
        have h_inf_xz_nn :=
          correlationInfinite_latticeGraph_nonneg d Λ p hf {x₀, z}
        exact mul_le_mul_of_nonneg_left hyz_le h_inf_xz_nn

/-- **Per-stage pair-product nonnegativity** (ferromagnetic). -/
theorem correlationAlongExhaustion_pair_product_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (x₀ y₀ z : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {x₀, z} n *
        correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {y₀, z} n :=
  mul_nonneg (correlationAlongExhaustion_pair_nonneg d Λ p hf x₀ z n)
    (correlationAlongExhaustion_pair_nonneg d Λ p hf y₀ z n)

/-! ## Infinite-volume pair-product nonnegativity wrappers -/

/-- **Infinite-volume pair correlation nonnegativity** (ferromagnetic).
Convenience alias matching the per-stage wrappers above. -/
theorem correlationInfinite_pair_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z} :=
  correlationInfinite_latticeGraph_nonneg d Λ p hf {x, z}

/-- **Infinite-volume pair-product nonnegativity** (ferromagnetic). -/
theorem correlationInfinite_pair_product_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (x₀ y₀ z : Fin d → ℤ) :
    0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {x₀, z} *
        correlationInfinite (IsingModel.latticeGraph d) Λ p {y₀, z} :=
  mul_nonneg (correlationInfinite_pair_nonneg d Λ p hf x₀ z)
    (correlationInfinite_pair_nonneg d Λ p hf y₀ z)

/-! ## HLS sum existential as a summability witness -/

/-- **HLS sum bound implies infinite-volume pair-product nonneg, ≤ K**.

Repackages the HLS sum bound (#3188) in a form where the nonneg per-`z`
property is made explicit alongside the constant. -/
theorem tsum_correlationInfinite_pair_product_nonneg_le_K_of_simonLieb
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
      (∀ z : Fin d → ℤ,
        0 ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
          Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}) ∧
      ∑' z : Fin d → ℤ,
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
      hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
      h_corr_small h_adj_exp x₀ y₀
  refine ⟨K, hK_pos, ?_, hK_bound⟩
  intro z
  exact correlationInfinite_pair_product_nonneg d (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ, le_refl 0, hβ⟩ x₀ y₀ z

/-- **Existential positive K with `tsum ≤ K`** (alias for documentation
completeness alongside `tsum_correlationInfinite_pair_product_nonneg_le_K_of_simonLieb`).

Identical statement to
`tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent`
(#3188) — exposed under the per-stage wrappers file as the existential
positive-`K` bound on the infinite-volume pair-product tsum. -/
theorem tsum_correlationInfinite_pair_product_le_K_of_simonLieb_perstage_alias
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
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x₀, z} *
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {y₀, z}
      ≤ K :=
  tsum_correlationInfinite_pair_product_le_const_of_simonLieb_smallReg_adjacent
    hα hr d hαd hJ hβ hβJ_pos hβJd_pos hβJd_le hM_pos hMrate
    h_corr_small h_adj_exp x₀ y₀

end Ambient
end IsingModel
