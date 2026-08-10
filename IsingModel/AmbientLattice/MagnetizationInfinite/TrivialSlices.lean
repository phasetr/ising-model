import IsingModel.AmbientLattice.MagnetizationInfinite.HSymmetryBounds

/-!
# Trivial parameter slices and the tanh lower bound for the infinite-volume magnetization

Statements for an ambient graph `G : SimpleGraph V`, an exhaustion `Λ` of `V` and an ambient
site `i : V`, about `magnetizationInfinite G Λ p i`, the supremum over stages of the stage
magnetization at `i`.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`. The Prop-valued
hypotheses are exactly these: the lower bound assumes `0 ≤ J`, `0 ≤ h` and `0 < β`; the
noninteracting closed form assumes `Ferromagnetic ⟨0, h, β⟩`, whose content on that slice is
`0 ≤ h` and `0 < β`; and the vanishing statements assume nothing.

At `0 ≤ J`, `0 ≤ h` and `0 < β` the magnetization is bounded below by `Real.tanh (β * h)`, the
singleton case of the corresponding lower bound for the infinite-volume correlation. On the
noninteracting slice that bound is attained: the magnetization equals `Real.tanh (β * h)`,
which under `0 ≤ h` and `0 < β` lies in `Set.Ico 0 1` and vanishes exactly at `h = 0`.

The magnetization is `0`, with no hypothesis at all, on the infinite-temperature slice `β = 0`
and on the zero-field slice `h = 0`, where correlations of odd-cardinality test sets vanish by
the Z₂ spin-flip symmetry and the singleton is one of them. The zero-field statement agrees
with the closed form above, which also vanishes at `h = 0`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

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
