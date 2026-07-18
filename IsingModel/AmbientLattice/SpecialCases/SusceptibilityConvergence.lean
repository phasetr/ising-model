import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Susceptibility h/J/β → ∞ convergence wrappers along an exhaustion

Narrow child module for the finite-stage along-exhaustion
susceptibility convergence wrappers in the `h`, `J`, and `β`
directions:

* `susceptibilityAlongExhaustion_convergent_h_param`
* `susceptibilityAlongExhaustion_convergent_J_param`
* `susceptibilityAlongExhaustion_convergent_beta_param`

Theorem names are unchanged from the former monolithic
special-cases declarations. (Merged from the former
`SusceptibilityConvergenceBeta.lean` child — #4563 cycle-12
fixed-cost consolidation; statements and proofs preserved verbatim.)
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞)
along-ex wraps -/

/-- **Along-ex: susceptibility β → ∞ convergence**. Per-stage `n`. -/
theorem susceptibilityAlongExhaustion_convergent_beta_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_beta G (Λ.volume n) J hJ h hh _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility h → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_h_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_h G (Λ.volume n) J hJ β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility J → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_J_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_J G (Λ.volume n) h hh β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

end Ambient
end IsingModel
