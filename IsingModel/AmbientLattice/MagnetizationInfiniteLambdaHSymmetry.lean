import IsingModel.AmbientLattice.MagnetizationAlongExhaustion

/-!
# Ambient Λ-level h-symmetry / J_zero / tanh-power wrappers

Narrow child module for the Λ-level h-symmetry, odd-vanish at h=0,
J_zero, and tanh-power lower-bound wrappers (10 theorems):
`correlationΛ_odd_vanish_h_zero`, `correlationΛ_neg_h`,
`magnetizationΛ_neg_h`, `correlationΛ_eq_abs_h_of_even_card`,
`abs_magnetizationΛ_eq_magnetizationΛ_abs_h`,
`susceptibilityΛ_neg_h`, `susceptibilityΛ_eq_abs_h`,
`correlationΛ_J_zero`, `correlationΛ_ge_tanh_pow_card`,
`magnetizationΛ_ge_tanh`. The theorem names are unchanged from the
former `MagnetizationInfinite` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Z₂ symmetry at `h = 0` for `correlationΛ`**: at vanishing external
field, the correlation on `Λ` of an odd-cardinality set is zero.
Lift of `IsingModel.correlation_odd_vanish` (GHS.lean). -/
theorem correlationΛ_odd_vanish_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ G Λ ⟨J, 0, β⟩ A = 0 :=
  IsingModel.correlation_odd_vanish (inducedGraph G Λ) J β A hodd

/-- **Z₂ odd-symmetry for `correlationΛ` under `h → -h`**:
`correlationΛ G Λ ⟨J, -h, β⟩ A = (-1)^|A| · correlationΛ G Λ ⟨J, h, β⟩ A`.
Λ-level lift of `IsingModel.correlation_neg_h`. Generalizes
`correlationΛ_odd_vanish_h_zero` from `h = 0` to arbitrary `h`. -/
theorem correlationΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_neg_h (inducedGraph G Λ) J h β A

/-- **Z₂ odd-symmetry for `magnetizationΛ` under `h → -h`**:
`magnetizationΛ G Λ ⟨J, -h, β⟩ i = -magnetizationΛ G Λ ⟨J, h, β⟩ i`.
Direct specialization of `correlationΛ_neg_h` at `A = {i}`
(card 1, `(-1)^1 = -1`). -/
theorem magnetizationΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    magnetizationΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  unfold magnetizationΛ
  rw [correlationΛ_neg_h, Finset.card_singleton, pow_one]
  ring

/-- **Λ-level `correlation_eq_abs_h_of_even_card`**: for `|A|` even,
`correlationΛ G Λ ⟨J, h, β⟩ A = correlationΛ G Λ ⟨J, |h|, β⟩ A`.
Λ-layer lift of `IsingModel.correlation_eq_abs_h_of_even_card`. -/
theorem correlationΛ_eq_abs_h_of_even_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (A : Finset (↑Λ : Type _)) (heven : Even A.card) :
    correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_abs_h_of_even_card (inducedGraph G Λ) J h β A heven

/-- **Λ-layer `|M_Λ(h)| = M_Λ(|h|)`** under ferromagnetism at `|h|`:
requires `0 ≤ J ∧ 0 < β` (so that `Ferromagnetic ⟨J, |h|, β⟩` holds
automatically via `0 ≤ |h|`). Λ-layer counterpart of
`IsingModel.abs_magnetization_eq_magnetization_abs_h` (PR #769).

Proof by `abs_choice h`: at `|h| = h` (`h ≥ 0`),
`magnetizationΛ_nonneg` gives the nonneg value matches `|·|`; at
`|h| = -h` (`h ≤ 0`), `magnetizationΛ_neg_h` flips sign and the
ferromagnetic nonnegativity at `|h|` makes the absolute value agree.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 (background). -/
theorem abs_magnetizationΛ_eq_magnetizationΛ_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : (↑Λ : Type _)) :
    |magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i|
      = magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
    ⟨hJ, abs_nonneg _, hβ⟩
  have habs_nonneg :
      0 ≤ magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
    magnetizationΛ_nonneg G Λ _ hf_abs i
  rcases abs_choice h with habs | habs
  · -- |h| = h (h ≥ 0)
    have heq :
        magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          = magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [habs]
    rw [heq]
    apply abs_of_nonneg
    have h_ge : 0 ≤ h := by rw [← habs]; exact abs_nonneg h
    exact magnetizationΛ_nonneg G Λ _ ⟨hJ, h_ge, hβ⟩ i
  · -- |h| = -h (h ≤ 0)
    have hneg :
        magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          = -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [habs]; exact magnetizationΛ_neg_h G Λ J h β i
    rw [hneg]
    apply abs_of_nonpos
    have hne :
        0 ≤ -magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
      rw [← hneg]; exact habs_nonneg
    linarith

/-- **Λ-level susceptibility under `h → -h`**:
`χ_Λ(J, -h, β; i) = χ_Λ(J, h, β; i) - 2·M_Λ(J, h, β; i)`.
Direct lift of `IsingModel.susceptibility_neg_h` through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)` and
`magnetizationΛ = IsingModel.magnetization (inducedGraph G Λ)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_neg_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    susceptibilityΛ G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
          - 2 * magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_neg_h (inducedGraph G Λ) J h β i

/-- **Λ-level susceptibility closed form at `|h|`** (A-4, capstone):
`χ_Λ(J, |h|, β; i) = χ_Λ(J, h, β; i) + M_Λ(J, |h|, β; i) - M_Λ(J, h, β; i)`,
unconditionally (no ferromagnetic hypothesis required).

Direct lift of `IsingModel.susceptibility_eq_abs_h` (PR #771) through
`susceptibilityΛ := IsingModel.susceptibility (inducedGraph G Λ)` and
`magnetizationΛ = IsingModel.magnetization (inducedGraph G Λ)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_eq_abs_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J h β : ℝ) (i : (↑Λ : Type _)) :
    susceptibilityΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
          + magnetizationΛ G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i
          - magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_eq_abs_h (inducedGraph G Λ) J h β i

/-- **Λ-level correlation closed form at `J = 0`**:
`correlationΛ G Λ ⟨0, h, β⟩ A = tanh(β·h)^A.card`. Direct lift of
`IsingModel.correlation_J_zero` through
`correlationΛ := correlation (inducedGraph G Λ)`. Unconditional. -/
theorem correlationΛ_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h β : ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  IsingModel.correlation_J_zero (inducedGraph G Λ) h β A

/-- **Λ-level lower bound `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic,
sharp): by J-monotonicity from `J = 0` (where `correlationΛ = tanh(β·h)^|A|`)
up to any `J ≥ 0`. -/
theorem correlationΛ_ge_tanh_pow_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  have h_zero : correlationΛ G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card := correlationΛ_J_zero G Λ h β A
  rw [← h_zero]
  exact correlationΛ_monotone_J G Λ hh hβ A
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hJ) hJ

/-- **Λ-level lower bound `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic):
specialization of `correlationΛ_ge_tanh_pow_card` at `A = {i}` where
`|A|^1 = |A|.card = 1`. -/
theorem magnetizationΛ_ge_tanh
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  have := correlationΛ_ge_tanh_pow_card G Λ hJ hh hβ ({i} : Finset (↑Λ : Type _))
  simpa [Finset.card_singleton] using this


end Ambient

end IsingModel
