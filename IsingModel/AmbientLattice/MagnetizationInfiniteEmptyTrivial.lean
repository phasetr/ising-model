import IsingModel.AmbientLattice.CorrelationInfinite.Basic

/-!
# Ambient empty / beta_zero / zero_params correlation wrappers

Narrow child module for the empty-set normalization + beta_zero vanish +
zero_params vanish wrappers (9 theorems): `correlationΛ_empty`,
`correlationAlongExhaustion_empty`, `correlationInfinite_empty`,
`correlationΛ_beta_zero_vanish_of_nonempty`,
`correlationAlongExhaustion_beta_zero_vanish`,
`correlationInfinite_beta_zero_vanish`,
`correlationΛ_zero_params_vanish_of_nonempty`,
`correlationAlongExhaustion_zero_params_vanish`,
`correlationInfinite_zero_params_vanish`. The theorem names are
unchanged from the former `MagnetizationInfinite` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Empty-set correlation on `Λ` is `1`** (normalization). -/
@[simp]
theorem correlationΛ_empty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (p : IsingParams ℝ) :
    correlationΛ G Λ p ∅ = 1 :=
  IsingModel.correlation_empty (inducedGraph G Λ) p

/-- **Empty-set correlation along exhaustion is `1`** for every `n`.
Empty set is always a subset of `Λ.volume n`, so the `dite` branch
always returns `correlationΛ G (Λ.volume n) p (liftFinset ∅ _) = 1`. -/
@[simp]
theorem correlationAlongExhaustion_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion G Λ p ∅ n = 1 := by
  unfold correlationAlongExhaustion
  have hsub : (∅ : Finset V) ⊆ Λ.volume n := Finset.empty_subset _
  rw [dif_pos hsub]
  have hlift : liftFinset (∅ : Finset V) hsub = (∅ : Finset (↑(Λ.volume n) : Type _)) := by
    simp [liftFinset]
  rw [hlift, correlationΛ_empty]

/-- **Infinite-volume empty-set correlation is `1`**:
`ciSup` of the constantly-one sequence. -/
@[simp]
theorem correlationInfinite_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    correlationInfinite G Λ p ∅ = 1 := by
  simp only [correlationInfinite, correlationAlongExhaustion_empty, ciSup_const]

/-- **β=0 correlation vanishes on `Λ`**: at `β = 0` every nonempty
`A : Finset (↑Λ)` gives `correlationΛ = 0`. Lift of PR #182
`correlation_beta_zero_vanish_of_nonempty_A`
(`Inequalities/NonnegCorrelations.lean`). -/
theorem correlationΛ_beta_zero_vanish_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h : ℝ) (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    (inducedGraph G Λ) J h A hA

/-- **β=0 correlation vanishes along exhaustion**: pointwise zero
at every `n` for nonempty `A : Finset V`. Either `A ⊄ Λ.volume n`
(dite gives 0) or `A ⊆ Λ.volume n` and the lifted correlation
vanishes via `correlationΛ_beta_zero_vanish_of_nonempty`. -/
theorem correlationAlongExhaustion_beta_zero_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨J, h, 0⟩ : IsingParams ℝ) hAn]
    refine correlationΛ_beta_zero_vanish_of_nonempty G (Λ.volume n) J h _ ?_
    obtain ⟨a, haA⟩ := hA
    exact ⟨⟨a, hAn haA⟩, by simp [liftFinset, haA]⟩
  · exact correlationAlongExhaustion_of_not_subset G Λ (⟨J, h, 0⟩ : IsingParams ℝ) hAn

/-- **β=0 correlation vanishes at infinite volume**: the stagewise
zero sequence has supremum zero. -/
theorem correlationInfinite_beta_zero_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (A : Finset V) (hA : A.Nonempty) :
    correlationInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_beta_zero_vanish G Λ J h A hA, ciSup_const]

/-- **J=h=0 correlation vanishes on `Λ`**: at zero parameters every
nonempty `A : Finset (↑Λ)` gives `correlationΛ = 0`. Lift of PR #188
`correlation_zero_params_vanish_of_nonempty_A`. -/
theorem correlationΛ_zero_params_vanish_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β : ℝ) (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_zero_params_vanish_of_nonempty_A
    (inducedGraph G Λ) β A hA

/-- **J=h=0 correlation vanishes along exhaustion**: pointwise zero
at every `n` for nonempty `A`. `dite` branches reduce to either 0
(off branch) or the Λ lift with nonempty `liftFinset`. -/
theorem correlationAlongExhaustion_zero_params_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (A : Finset V) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨0, 0, β⟩ : IsingParams ℝ) hAn]
    refine correlationΛ_zero_params_vanish_of_nonempty G (Λ.volume n) β _ ?_
    obtain ⟨a, haA⟩ := hA
    exact ⟨⟨a, hAn haA⟩, by simp [liftFinset, haA]⟩
  · exact correlationAlongExhaustion_of_not_subset G Λ (⟨0, 0, β⟩ : IsingParams ℝ) hAn

/-- **J=h=0 correlation vanishes at infinite volume**: `ciSup` of
the constantly-zero sequence. -/
theorem correlationInfinite_zero_params_vanish
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (A : Finset V) (hA : A.Nonempty) :
    correlationInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_zero_params_vanish G Λ β A hA, ciSup_const]

end Ambient

end IsingModel
