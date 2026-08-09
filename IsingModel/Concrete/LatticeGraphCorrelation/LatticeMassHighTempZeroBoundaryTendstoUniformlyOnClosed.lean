import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundary
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempZeroBoundaryContinuousOnClosed

/-!
# ℤ^d uniform convergence on a closed interval from the origin

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the uniform convergence of the
finite-volume correlations to the infinite-volume one on `Set.Icc 0 b`, in the
inverse-temperature direction and in the coupling direction. Each convergence statement
assumes `1 ≤ d`, distinctness of the two sites, `0 < b`, strict positivity of the parameter
held fixed, and that `b` times that parameter times `2 * d` is below one. Each rests on the
observation, recorded here at a fixed exhaustion stage, that the finite-volume correlation
vanishes when the parameter being varied is zero; those observations hold for an arbitrary
pair of sites, not assumed distinct, and carry no hypothesis.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Helper: corr_n vanishes at β = 0** (Step 178 helper):
At β = 0, the finite-volume correlation along exhaustion is zero. -/
lemma correlationAlongExhaustion_eq_zero_at_beta_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (J : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨J, 0, 0⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_beta_zero_vanish_of_nonempty_A _ J 0 _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed interval [0, b]** (Step 178):
Strengthens Step 170 to include β = 0.

Proof: Apply Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the
compact interval `[0, b]` using continuity of each corr_n, monotonicity in n
(at β = 0 it's trivial since both sides are 0), continuity of corr_∞ (Step 177),
and pointwise convergence. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_beta_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * J * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · -- (1) ContinuousOn of each corr_n on [0, b]
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
  · -- (2) Monotone in n for each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: corr_n(0) = 0 for all n, monotone trivially
      subst hβ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero, le_refl]
    · -- β > 0: use the standard monotone theorem
      exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) Continuity of corr_∞ on [0, b] (Step 177)
    exact correlationInfinite_continuousOn_beta_of_high_temp_zero_closed
      hd Λ r_val s_val hrs J hJ_pos b hb_pos hlt
  · -- (4) Pointwise convergence at each β ∈ [0, b]
    intro β hβ
    rcases eq_or_lt_of_le hβ.1 with hβ0 | hβ_pos
    · -- β = 0: both corr_n(0) and corr_∞(0) are 0
      subst hβ0
      simp only [correlationAlongExhaustion_eq_zero_at_beta_zero,
                 correlationInfinite_eq_zero_at_beta_zero]
      exact tendsto_const_nhds
    · -- β > 0: use correlationAlongExhaustion_tendsto_ciSup
      have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
        ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
      have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
        (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
      rw [correlationInfinite_eq_ciSup]
      exact htend

/-- **Helper: corr_n vanishes at J = 0** (Step 232 helper):
At J = h = 0 (any β), the finite-volume correlation along exhaustion is zero. -/
lemma correlationAlongExhaustion_eq_zero_at_J_zero
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (β : ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n = 0 := by
  by_cases h_sub : ({r_val, s_val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · have hrn : r_val ∈ Λ.volume n := Finset.insert_subset_iff.mp h_sub |>.1
    have hsn : s_val ∈ Λ.volume n :=
      Finset.singleton_subset_iff.mp (Finset.insert_subset_iff.mp h_sub |>.2)
    have heq : correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨0, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n =
               IsingModel.correlation
                  (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                  (⟨0, 0, β⟩ : IsingParams ℝ) {(⟨r_val, hrn⟩ : ↑(Λ.volume n)),
                                                ⟨s_val, hsn⟩} := by
      rw [correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
      congr 1
      ext u; rw [mem_liftFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [heq]
    exact IsingModel.correlation_zero_params_vanish_of_nonempty_A _ β _
      (Finset.insert_nonempty _ _)
  · rw [correlationAlongExhaustion_of_not_subset _ _ _ h_sub]

/-- **TendstoUniformlyOn corr_n → corr_∞ on closed [0, b] in J including J = 0** (Step 232):
For `0 < β`, `0 < b`, `bβ·2d < 1`: corr_n → corr_∞ uniformly on `[0, b]` in J at h = 0.

Direct J-direction analogue of Step 178. Strengthens Step 224 to include J = 0.
Proof: Dini's theorem (`Monotone.tendstoUniformlyOn_of_forall_tendsto`) on the compact
[0, b] with: (1) ContinuousOn each corr_n; (2) Monotonicity in n at J = 0 trivial,
at J > 0 from `correlationAlongExhaustion_monotone`; (3) ContinuousOn corr_∞ from
Step 231; (4) pointwise convergence at J = 0 trivial, at J > 0 from
`correlationAlongExhaustion_tendsto_ciSup`. -/
theorem correlationAlongExhaustion_tendstoUniformlyOn_J_zero_closed
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β)
    (b : ℝ) (hb_pos : 0 < b) (hlt : b * β * ↑(2 * d) < 1) :
    TendstoUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Icc 0 b) := by
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
  · intro J hJ
    rcases eq_or_lt_of_le hJ.1 with hJ0 | hJ_pos
    · subst hJ0
      intro n m _
      simp only [correlationAlongExhaustion_eq_zero_at_J_zero, le_refl]
    · exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_zero_closed
      hd Λ r_val s_val hrs β hβ_pos b hb_pos hlt
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
