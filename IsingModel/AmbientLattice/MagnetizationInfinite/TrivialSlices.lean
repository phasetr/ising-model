import IsingModel.AmbientLattice.MagnetizationInfinite.HSymmetryBounds

/-!
# Infinite-volume magnetization trivial slices

`tanh`, β=0, J=0, and h=0 wrappers for `magnetizationInfinite`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Moved: h_zero / J_zero / zero_params / tanh_pow wrappers

The 8 h_zero / J_zero / zero_params / tanh_pow wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteHZeroJZero`.
The earlier import path is preserved by re-importing the new child.
The closely related `magnetizationInfinite_ge_tanh` stays here because
it references `magnetizationInfinite` directly.
-/

/-- **∞-volume lower bound `magnetizationInfinite ≥ tanh(β·h)`**
(ferromagnetic): specialization of `correlationInfinite_ge_tanh_pow_card`
at `A = {i}`. -/
theorem magnetizationInfinite_ge_tanh
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : V) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
  have := correlationInfinite_ge_tanh_pow_card G Λ hJ hh hβ ({i} : Finset V)
  simpa [Finset.card_singleton] using this


/-! ## Moved: empty / beta_zero / zero_params correlation wrappers

The 9 empty / beta_zero_vanish / zero_params_vanish wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteEmptyTrivial`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: magnetizationΛ / magnetizationAlongExhaustion trivial-slice wrappers

The 7 magnetizationΛ / magnetizationAlongExhaustion trivial-slice
wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteMagTrivial`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **β=0 infinite-volume magnetization vanishes**: at infinite
temperature (`β = 0`), spins are uniformly distributed and decoupled,
so the thermodynamic magnetization is `0` at every site.

Specialization of `correlationInfinite_beta_zero_vanish` at the
singleton `{i}` (automatically nonempty). -/
theorem magnetizationInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) :
    magnetizationInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  correlationInfinite_beta_zero_vanish G Λ J h {i} (by simp)

/-- **`magnetizationInfinite` closed form at `J = 0`** (ferromagnetic):
`magnetizationInfinite G Λ ⟨0, h, β⟩ i = tanh(β·h)`.

Specialization of `correlationInfinite_J_zero`
(`⟨σ^A⟩_∞ = tanh(β·h)^|A|`, PR #210) at the singleton `{i}`
(`A.card = 1`, so the power reduces to `tanh(β·h)`).

Complements `magnetizationInfinite_beta_zero` (β=0: vanishes) and
`magnetizationInfinite_zero_at_h_zero` (h=0: vanishes).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(non-interacting `J = 0` slice; `β` is constrained only by
`Ferromagnetic.hβ : 0 < β`, not by the infinite-temperature
limit `β → 0`); §5.1 pp. 76–77 (magnetization). -/
theorem magnetizationInfinite_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) := by
  unfold magnetizationInfinite
  rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]

/-- **`magnetizationInfinite` at `h = 0` vanishes**: the Z₂ spin-flip
symmetry at zero external field forces the single-site thermodynamic
magnetization to be zero.

This gives the zero-field **symmetric** value, which is distinct from
the *spontaneous magnetization* $m^* := \lim_{h \to 0^+} M(h)$ studied
in Glimm–Jaffe §5.1 (p. 77): symmetry breaking is detected by the
one-sided limit $h \to 0^+$ (or boundary-condition selection), not by
evaluating at $h = 0$. -/
theorem magnetizationInfinite_zero_at_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    magnetizationInfinite G Λ ⟨J, 0, β⟩ i = 0 :=
  correlationInfinite_h_zero G Λ J β {i} (by simp)

end Ambient
end IsingModel
