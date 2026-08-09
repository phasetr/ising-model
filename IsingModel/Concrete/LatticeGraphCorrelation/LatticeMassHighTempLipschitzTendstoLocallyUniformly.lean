import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempLipschitzContinuousOnOpen
import Mathlib.Topology.UniformSpace.Dini

/-!
# ℤ^d locally uniform convergence on the open high-temperature interval

Instantiates at `IsingModel.latticeGraph d`, for an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ` and two distinct sites at zero external field, the locally uniform convergence of
the finite-volume correlations to the infinite-volume one on the open interval `Set.Ioo 0 c`,
where `c` is the reciprocal of `2 * d` times the parameter held fixed. The statement is given
in the inverse-temperature direction and in the coupling direction, and each assumes `1 ≤ d`,
distinctness of the two sites, and strict positivity of the parameter held fixed.
-/

namespace IsingModel
namespace Ambient

/-- **Locally uniform convergence corr_n → corr_∞ on open high-temperature interval** (Step 174):
For `0 < J`, `1 ≤ d`: the finite-volume two-point functions converge locally uniformly to
the infinite-volume limit on the open interval `Ioo 0 (1/(J·2d))`.

Proof: Apply `Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto` (Mathlib Dini) on
the open set `Ioo 0 β_c` using:
1. ContinuousOn of each corr_n (from `correlation_continuousAt_beta`).
2. Monotonicity in n (from `correlationAlongExhaustion_monotone`).
3. ContinuousOn of corr_∞ (Step 173).
4. Pointwise convergence (`correlationAlongExhaustion_tendsto_ciSup`).

Strengthens Step 170 from a fixed compact `[a, b]` to locally uniform on `Ioo 0 β_c`. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_beta_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (J : ℝ) (hJ_pos : 0 < J) :
    TendstoLocallyUniformlyOn
      (fun n β => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun β => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · -- (1) Continuity of each corr_n in β on the open interval
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
  · -- (2) Monotone in n for each β ∈ Ioo 0 β_c
    intro β hβ
    have hβ_pos : 0 < β := hβ.1
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · -- (3) Continuity of the limit on Ioo 0 β_c (Step 173)
    exact correlationInfinite_continuousOn_beta_of_high_temp_open hd Λ r_val s_val hrs J hJ_pos
  · -- (4) Pointwise convergence
    intro β hβ
    have hβ_pos : 0 < β := hβ.1
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

/-- **Locally uniform convergence of corr_n → corr_∞ on Ioo 0 J_c in J** (Step 228):
For `0 < β`, `1 ≤ d`: corr_n → corr_∞ locally uniformly on `Ioo 0 (1/(β·2d))`.

Direct J-direction analogue of Step 174. Proof:
`Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto` with
(1) ContinuousOn each corr_n in J; (2) Monotonicity in n; (3) ContinuousOn corr_∞ (Step 227);
(4) pointwise convergence. Strengthens Step 224 from compact `[a, b]` to locally uniform on
`Ioo 0 J_c`. -/
theorem correlationAlongExhaustion_tendstoLocallyUniformlyOn_J_of_high_temp_open
    {d : ℕ} (hd : 1 ≤ d) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (r_val s_val : Fin d → ℤ) (hrs : r_val ≠ s_val)
    (β : ℝ) (hβ_pos : 0 < β) :
    TendstoLocallyUniformlyOn
      (fun n J => correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) {r_val, s_val} n)
      (fun J => correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
                    {r_val, s_val})
      Filter.atTop (Set.Ioo (0 : ℝ) (1 / (β * ↑(2 * d)))) := by
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
  · intro J hJ_mem
    have hJ_pos : 0 < J := hJ_mem.1
    exact correlationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hJ_pos.le, le_refl 0, hβ_pos⟩ {r_val, s_val}
  · exact correlationInfinite_continuousOn_J_of_high_temp_open hd Λ r_val s_val hrs β hβ_pos
  · intro J hJ_mem
    have hJ_pos : 0 < J := hJ_mem.1
    have hf : IsingModel.Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
    have htend := IsingModel.Ambient.correlationAlongExhaustion_tendsto_ciSup
      (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) hf {r_val, s_val}
    simp only [correlationInfinite_eq_ciSup]
    exact htend

end Ambient
end IsingModel
