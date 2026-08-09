import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitz.Continuity

/-!
# ℤ^d uniform convergence on a compact interval, and a.e. differentiability

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the uniform convergence of the
finite-volume correlations to the infinite-volume one on a compact interval `Set.Icc a b`
with `0 < a ≤ b`, and the differentiability of the limit within that interval at
Lebesgue-almost every point. Each is given in the inverse-temperature direction, where the
coupling satisfies `0 ≤ J`, and in the coupling direction, where the inverse temperature
satisfies `0 < β`; in each direction the high-temperature condition is that `b` times the
parameter held fixed times `2 * d` is below one. No condition is placed on the dimension.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Uniform convergence of finite-volume correlations** (Step 170, GJ §17.5):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]`:
`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ β ∈ [a,b], |corr_n(β) - corr_∞(β)| < ε`.

In Lean: `TendstoUniformlyOn (fun n β => corr_n(β)) (fun β => corr_∞(β)) atTop (Set.Icc a b)`.

Proof: Dini's theorem (`tendstoUniformlyOn_of_forall_tendsto`) on the compact set `[a, b]`:
1. Each `β ↦ corr_n(β)` is continuous on `[a,b]` (Step 117a for finite-vol case,
   constant 0 otherwise).
2. For each `β ∈ [a,b]`, `n ↦ corr_n(β)` is monotone (`correlationAlongExhaustion_monotone`).
3. The limit `β ↦ corr_∞(β)` is continuous on `[a,b]` (Step 169).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`).

Reference: Glimm–Jaffe §17.5 p.~312 (monotone convergence to thermodynamic limit). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) Continuity of each corr_n in β
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      -- Each β ↦ correlation G_n ⟨J,0,β⟩ {r,s} is continuous (Step 117a)
      intro β _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun β' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun β' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext β'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact IsingModel.correlation_continuousAt_beta _ J β _
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · -- (2) Monotone in n for each β ∈ [a, b]
    intro β hβ
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩ {r_val, s_val}
  · -- (3) Continuity of the limit (Step 169)
    exact correlationInfinite_continuousOn_beta_of_high_temp Λ r_val s_val hrs J hJ a b ha hab hlt
  · -- (4) Pointwise convergence
    intro β hβ
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl 0, ha.trans_le hβ.1⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **Uniform convergence of finite-volume correlations in J** (Step 224):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
the finite-volume two-point functions converge uniformly on `[a, b]` in J.

Direct J-direction analogue of Step 170. Proof: Dini's theorem on the compact `[a, b]`:
1. Each `J ↦ corr_n(J)` is continuous (Step 207 + `.continuousAt`).
2. `n ↦ corr_n(J)` is monotone (`correlationAlongExhaustion_monotone`).
3. Limit `J ↦ corr_∞(J)` is continuous (Step 223).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`). -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
      intro J _
      apply ContinuousAt.continuousWithinAt
      have heq : (fun J' => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J', 0, β⟩ : IsingParams ℝ) {r_val, s_val} n) =
                 (fun J' => IsingModel.correlation
                    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                    (⟨J', 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                    ⟨s_val, hsn⟩}) := by
        funext J'
        rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
        congr 1
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [heq]
      exact (IsingModel.correlation_continuous_J _ 0 β _).continuousAt
    · simp only [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]
      exact continuousOn_const
  · intro J hJ_mem
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ)
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp Λ r_val s_val hrs β hβ a b ha hab hlt
  · intro J hJ_mem
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨le_of_lt (ha.trans_le hJ_mem.1), le_refl 0, hβ⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **A.e. differentiability of infinite-volume two-point function in β** (Step 171):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 ≤ J`, `0 < a ≤ b`, `bJ·2d < 1`,
the infinite-volume two-point function `β ↦ corr_∞(β)` is differentiable within `[a,b]`
at Lebesgue-almost every `β ∈ [a,b]`.

Proof: direct from Step 168 (`correlationInfinite_lipschitzOnWith_beta_of_high_temp`)
via Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`).

Analytic corollary of the Lipschitz bound established in the GJ §17.5 derivative program.
Not yet the full everywhere-differentiability claimed by GJ §17.6 Thm 17.6.1 p.313
(that requires uniform convergence of the derivative sequence). -/
theorem correlationInfinite_ae_differentiableWithinAt_beta_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ : 0 ≤ J)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * J * ↑(2 * d) < 1) :
    ∀ᵐ β ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) β := by
  have hlip := correlationInfinite_lipschitzOnWith_beta_of_high_temp
    Λ r_val s_val hrs J hJ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

/-- **A.e. differentiability of infinite-volume two-point function in J** (Step 225):
For any exhaustion `Λ`, vertices `r_val ≠ s_val`, `0 < β`, `0 < a ≤ b`, `bβ·2d < 1`,
`J ↦ corr_∞(J)` is differentiable within `[a, b]` at Lebesgue-a.e. J.

Direct J-direction analogue of Step 171. Proof: Step 222 (Lipschitz) +
Rademacher's theorem (`LipschitzOnWith.ae_differentiableWithinAt_real`). -/
theorem correlationInfinite_ae_differentiableWithinAt_J_of_high_temp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlt : b * β * ↑(2 * d) < 1) :
    ∀ᵐ J ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc a b),
    DifferentiableWithinAt ℝ
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      (Set.Icc a b) J := by
  have hlip := correlationInfinite_lipschitzOnWith_J_of_high_temp
    Λ r_val s_val hrs β hβ a b ha hab hlt
  exact LipschitzOnWith.ae_differentiableWithinAt_real hlip measurableSet_Icc

end Ambient
end IsingModel
