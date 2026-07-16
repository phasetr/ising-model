import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry

/-!
# Ambient susceptibilityInfinite definition + wrappers

Narrow child module for the infinite-volume susceptibility definition
`susceptibilityInfinite` and its 4 properties
(`susceptibilityInfinite_eq_ciSup`, `_apply`, `_nonneg`, `_le_abs_h`).
The definition and theorem names are unchanged from the former
`MagnetizationInfinite` declarations. The h-symmetry consequence
`abs_magnetizationInfinite_le_magnetizationInfinite_abs_h` was
intentionally left in the parent because it directly references
`magnetizationInfinite` which still lives there.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Infinite-volume susceptibility** at site `i : V`:
`susceptibilityInfinite G Λ p i := ⨆ n, susceptibilityAlongExhaustion G Λ p i n`.

Analog of `magnetizationInfinite` / `correlationInfinite`, but for the
susceptibility χ. Unlike `correlation` (bounded by 1) or
`magnetization` (bounded by 1), susceptibility is *not automatically
bounded* as the exhaustion grows: `|χ_Λ(i)| ≤ 2·|Λ|`, which diverges
with `|Λ|`. Hence the `⨆` on `ℝ` may return the `ciSup` default `0`
when the along-exhaustion sequence is unbounded (physically: near or at
the critical point, where χ diverges in the genuine thermodynamic
limit). Theorems that compare `susceptibilityInfinite` values
typically require an explicit `BddAbove` hypothesis in the unbounded
case (see `susceptibilityInfinite_le_abs_h` below).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
noncomputable def susceptibilityInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℝ :=
  ⨆ n, susceptibilityAlongExhaustion G Λ p i n

/-- **`susceptibilityInfinite` as `ciSup`**:
`susceptibilityInfinite G Λ p i = ⨆ n, susceptibilityAlongExhaustion G Λ p i n`
(named restatement of the definition for use in rewrites). -/
theorem susceptibilityInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    susceptibilityInfinite G Λ p i
      = ⨆ n, susceptibilityAlongExhaustion G Λ p i n := rfl

/-- **Nonnegativity of `susceptibilityInfinite`** under ferromagnetism:
`0 ≤ susceptibilityInfinite G Λ p i`.

Proof: each `susceptibilityAlongExhaustion … n` is `≥ 0` by
`susceptibilityAlongExhaustion_nonneg`; the `⨆` of a pointwise-nonneg
sequence on `ℝ` is `≥ 0` regardless of whether the sequence is
bounded above (if unbounded, `ciSup` defaults to `0`, which is still
`≥ 0`). -/
theorem susceptibilityInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ susceptibilityInfinite G Λ p i := by
  unfold susceptibilityInfinite
  by_cases hbd :
      BddAbove (Set.range fun n => susceptibilityAlongExhaustion G Λ p i n)
  · exact le_ciSup_of_le hbd 0
      (susceptibilityAlongExhaustion_nonneg G Λ p hf i 0)
  · rw [Real.iSup_of_not_bddAbove hbd]

/-- **∞-volume one-sided `χ_∞(h) ≤ χ_∞(|h|)`** (A-5′) under
`0 ≤ J`, `0 < β`, **assuming** `BddAbove` of the `|h|`-side
along-exhaustion sequence.

Stage-wise pointwise inequality `χ_along(h) ≤ χ_along(|h|)` at every
`n` (A-4c, PR #780) transfers to the `⨆` once the `|h|`-side is
known to be bounded above. Under the `BddAbove` hypothesis, the
pointwise comparison plus `ciSup_le_ciSup` gives the result.

**Necessity of `BddAbove`**: the susceptibility is unbounded at the
ferromagnetic critical point, where `⨆ χ_along(|h|)` would default to
`0` via the `ciSup` convention on unbounded sets. Away from the critical
line (high-temperature or deep ferromagnetic pure phases) the `BddAbove`
hypothesis is expected to hold.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityInfinite_le_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V)
    (hbd : BddAbove (Set.range fun n =>
      susceptibilityAlongExhaustion G Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n)) :
    susceptibilityInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i
      ≤ susceptibilityInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  unfold susceptibilityInfinite
  refine ciSup_mono hbd ?_
  intro n
  exact susceptibilityAlongExhaustion_le_abs_h G Λ J h β hJ hβ i n

end Ambient

end IsingModel
