import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Magnetization convergence wrappers along an exhaustion

Narrow child module for finite-stage magnetization convergence wrappers along
an exhaustion. The theorem names are the same as the former
declarations, but callers can now avoid importing the monolithic special-cases
original module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### magnetization parameter-direction convergent (β/h/J → ∞)
along-ex wraps -/

/-- **Along-ex: magnetization β → ∞ convergence**. Per-stage `n`. -/
theorem magnetizationAlongExhaustion_convergent_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_beta G (Λ.volume n) J hJ h hh _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: magnetization h → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_convergent_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_h G (Λ.volume n) J hJ β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: magnetization J → ∞ convergence**. -/
theorem magnetizationAlongExhaustion_convergent_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => magnetizationΛ G (Λ.volume n)
          (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_pos]
      rfl
    rw [h_eq]
    exact magnetizationΛ_convergent_J G (Λ.volume n) h hh β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => magnetizationAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold magnetizationAlongExhaustion correlationAlongExhaustion
      simp only [Finset.singleton_subset_iff, hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

end Ambient
end IsingModel
