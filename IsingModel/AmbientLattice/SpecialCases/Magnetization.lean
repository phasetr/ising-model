import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion

/-!
# Magnetization along an exhaustion: regularity & convergence wrappers

Merged from 10 former per-theorem SpecialCases modules
(`Magnetization{Convergence,ConvergenceBeta,Regularity,RegularityAt,
RegularityAtContinuousAtBeta,RegularityAtDifferentiableAt,
RegularityAtDifferentiableAtBeta,RegularityContinuousBeta,
RegularityDifferentiable,RegularityDifferentiableBeta}.lean`) as part of
the #4563 cycle-10 fixed-cost consolidation. All 15 theorem
names/statements are preserved verbatim; see the git history of the
deleted `Magnetization*.lean` for provenance.

Contents (finite-stage along-exhaustion wrappers, each a thin pass-through
to the corresponding ambient `magnetizationΛ_*` lemma):

* parameter-direction convergence (β/h/J → ∞);
* global `Continuous` / `Differentiable` regularity in β/h/J;
* the `h = 0` corollaries `magnetizationAlongExhaustion_{continuous,
  differentiable}_beta_gen`, re-homed here from
  `AmbientLattice/BetaDerivativeMagnetization.lean`;
* pointwise `ContinuousAt` / `DifferentiableAt` regularity in β/h/J.

The six global regularity proofs case-split on `{i} ⊆ Λ.volume n` through the
first-order family equations `correlationAlongExhaustion_family_eq_of_subset`
and `correlationAlongExhaustion_family_eq_zero_of_not_subset`
(`AmbientLattice/Exhaustion.lean`) instead of unfolding the `dite` by hand.
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

/-! ### magnetization regularity (`Continuous` / `Differentiable`)
along-ex wraps -/

/-- **Along-ex: magnetization Differentiable in `β`** (general h). -/
theorem magnetizationAlongExhaustion_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_differentiable_beta G (Λ.volume n) J h _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) hi]
    exact differentiable_const _

/-- **Along-ex: magnetization Continuous in `β`** (general h). -/
theorem magnetizationAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_continuous_beta G (Λ.volume n) J h _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun β' => (⟨J, h, β'⟩ : IsingParams ℝ)) hi]
    exact continuous_const

/-- **Along-ex: magnetization Differentiable in `β` at `h = 0`**
(Step 213, general `G`, `Λ`). The `h = 0` corollary of
`magnetizationAlongExhaustion_differentiable_beta`; kept as a named result
because Glimm–Jaffe §17.5 states the zero-field case separately. -/
theorem magnetizationAlongExhaustion_differentiable_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i n) :=
  magnetizationAlongExhaustion_differentiable_beta G Λ J 0 i n

/-- **Along-ex: magnetization Continuous in `β` at `h = 0`**
(Step 213, general `G`, `Λ`). The `h = 0` corollary of
`magnetizationAlongExhaustion_continuous_beta`; kept as a named result
because Glimm–Jaffe §17.5 states the zero-field case separately. -/
theorem magnetizationAlongExhaustion_continuous_beta_gen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    Continuous
      (fun β' => magnetizationAlongExhaustion G Λ (⟨J, 0, β'⟩ : IsingParams ℝ) i n) :=
  magnetizationAlongExhaustion_continuous_beta G Λ J 0 i n

/-- **Along-ex: magnetization Differentiable in `h`**. -/
theorem magnetizationAlongExhaustion_differentiable_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_differentiable_field G (Λ.volume n) J β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) hi]
    exact differentiable_const _

/-- **Along-ex: magnetization Differentiable in `J`**. -/
theorem magnetizationAlongExhaustion_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Differentiable ℝ (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_differentiable_J G (Λ.volume n) h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) hi]
    exact differentiable_const _

/-- **Along-ex: magnetization Continuous in `h` for `i ∈
Λ.volume n`**. The site coercion is the obvious lift. -/
theorem magnetizationAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_continuous_field G (Λ.volume n) J β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun h' => (⟨J, h', β⟩ : IsingParams ℝ)) hi]
    exact continuous_const

/-- **Along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_family_eq_of_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) hi]
    exact magnetizationΛ_continuous_J G (Λ.volume n) h β _
  · rw [correlationAlongExhaustion_family_eq_zero_of_not_subset G Λ
      (fun J' => (⟨J', h, β⟩ : IsingParams ℝ)) hi]
    exact continuous_const

/-! ### pointwise magnetization regularity
(`ContinuousAt` / `DifferentiableAt`) along-ex wraps -/

/-- **Along-ex: magnetization ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_continuous_beta G Λ J h i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_differentiable_beta G Λ J h i n).differentiableAt

/-- **Along-ex: magnetization DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_differentiable_field G Λ J β i n).differentiableAt

/-- **Along-ex: magnetization DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_differentiable_J G Λ h β i n).differentiableAt

/-- **Along-ex: magnetization ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_continuous_field G Λ J β i n).continuousAt

/-- **Along-ex: magnetization ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_continuous_J G Λ h β i n).continuousAt

end Ambient
end IsingModel
