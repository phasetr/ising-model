import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnIco
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryTendstoUniformlyOnClosed

/-!
# ℤ^d locally uniform convergence on the half-open high-temperature interval

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the locally uniform convergence of
the finite-volume correlations to the infinite-volume one on the half-open interval
`Set.Ico 0 c`, closed at the origin and open at the endpoint `c`, the reciprocal of `2 * d`
times the parameter held fixed. The statement is given in the inverse-temperature direction
and in the coupling direction, and each assumes `1 ≤ d`, distinctness of the two sites, and
strict positivity of the parameter held fixed.
-/

namespace IsingModel
namespace Ambient

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 β_c (half-open)** (Step 184):
For `0 < J`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(J·2d))`.

Combines Step 174 (Ioo 0 β_c) with Step 178 (Icc 0 b) via Dini's locally-uniform theorem
on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    TendstoLocallyUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · -- (1) ContinuousOn each corr_n on Ico 0 β_c
    intro n
    by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
    · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
      have hsn : s_val ∈ Λ.volume n :=
        Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
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
  · -- (2) Monotone in n at each β ∈ Ico 0 β_c
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) ContinuousOn corr_∞ on Ico 0 β_c (Step 182)
    exact correlationInfinite_continuousOn_beta_of_high_temp_Ico hd Λ r_val s_val hrs J hJ_pos
  · -- (4) Pointwise convergence
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **TendstoLocallyUniformlyOn corr_n → corr_∞ on Ico 0 J_c (half-open) in J** (Step 238):
For `0 < β`, `1 ≤ d`: corr_n converges locally uniformly to corr_∞ on `Ico 0 (1/(β·2d))` in J.

Direct J-direction analogue of Step 184. Combines Step 228 (Ioo 0 J_c) with Step 232
(Icc 0 b) via Dini's locally-uniform theorem on the half-open interval. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_J_Ico
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    TendstoLocallyUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ico (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
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
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_Ico hd Λ r_val s_val hrs β hβ_pos
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero,
                 correlationInfinite_eq_zero_at_J_zero]
      exact tendsto_const_nhds
    · have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

end Ambient
end IsingModel
