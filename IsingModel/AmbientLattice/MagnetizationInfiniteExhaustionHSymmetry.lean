import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry

/-!
# Behaviour of the stage and infinite-volume observables under reversal of the field

Statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`, about the
stage correlation, the stage magnetization and the stage susceptibility, together with the
infinite-volume correlation obtained as the supremum over stages.

Every declaration takes exactly two instance binders, `DecidableEq V` and the stagewise
`Fintype` instance on the edge set of the induced subgraph of `Λ.volume n`. The Prop-valued
hypotheses are exactly these: the zero-field vanishing statement assumes `Odd A.card`; the
infinite-volume statements assume `Even A.card`; the absolute-field magnetization identity and
the susceptibility comparison assume `0 ≤ J` and `0 < β`; and the reversal identities for the
stage correlation, the stage magnetization and the stage susceptibility, together with the
stage susceptibility identity at `|h|`, assume nothing.

Reversing the field multiplies the stage correlation by `(-1) ^ A.card`, with no hypothesis;
at the singleton test set that is a sign flip of the stage magnetization. At an odd test set
and zero field the stage correlation is therefore `0`.

At an even test set the stagewise sign is `1`, so the stagewise family is unchanged by the
reversal and the suprema agree. That gives invariance of the infinite-volume correlation under
reversal and, by splitting on which of `h` and `-h` is `|h|`, its equality with the value at
`|h|`.

At `0 ≤ J` and `0 < β` the absolute value of the stage magnetization at a field `h` equals its
value at `|h|`. For the stage susceptibility, reversal subtracts twice the stage
magnetization, and passing to `|h|` adds the difference of the stage magnetizations at `|h|`
and at `h`; these identities hold with no hypothesis. Under `0 ≤ J` and `0 < β` that
difference is nonnegative — it is `0` when `h` is already `|h|`, and twice the nonnegative
value at `|h|` otherwise — so the stage susceptibility at `h` is bounded above by its value at
`|h|`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`**:
pointwise zero at every `n`.  Either `A ⊄ Λ.volume n` (both branches
of the dite give `0`) or `A ⊆ Λ.volume n` and the lifted correlation
vanishes by `correlationΛ_odd_vanish_h_zero`. -/
theorem correlationAlongExhaustion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hAn]
    refine correlationΛ_odd_vanish_h_zero G (Λ.volume n) J β _ ?_
    rw [liftFinset_card hAn]
    exact hodd
  · exact correlationAlongExhaustion_of_not_subset G Λ ⟨J, 0, β⟩ hAn

/-- **Z₂ odd-symmetry under `h → -h` for `correlationAlongExhaustion`**:
at every stage `n`,
`corrAlongExh G Λ ⟨J,-h,β⟩ A n = (-1)^|A| · corrAlongExh G Λ ⟨J,h,β⟩ A n`
(Z₂ odd-symmetry under `h → -h`).

Case split on `A ⊆ Λ.volume n`: the else branch is `0`, and
`(-1)^|A| · 0 = 0`. Subset branch uses `correlationΛ_neg_h` +
`liftFinset_card` (preservation of cardinality under the lift).

Generalizes `correlationAlongExhaustion_h_zero` from `h = 0` (where
both sides are `0` at odd `|A|`) to arbitrary `h`. -/
theorem correlationAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A n
      = (-1) ^ A.card * correlationAlongExhaustion G Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A n := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ (⟨J, -h, β⟩ : IsingParams ℝ) hAn,
        correlationAlongExhaustion_of_subset G Λ (⟨J, h, β⟩ : IsingParams ℝ) hAn,
        correlationΛ_neg_h, liftFinset_card hAn]
  · rw [correlationAlongExhaustion_of_not_subset G Λ (⟨J, -h, β⟩ : IsingParams ℝ) hAn,
        correlationAlongExhaustion_of_not_subset G Λ (⟨J, h, β⟩ : IsingParams ℝ) hAn]
    ring

/-- **∞-volume `correlationInfinite` invariance under `h → -h`**
(for even `|A|`):
`correlationInfinite G Λ ⟨J, -h, β⟩ A = correlationInfinite G Λ ⟨J, h, β⟩ A`.

At even `|A|`, the pointwise `correlationAlongExhaustion_neg_h`
sign is `(-1)^|A| = 1`, so the sequence is unchanged and the
`ciSup` agrees. For odd `|A|` the sign flips, turning `ciSup` into
`-ciInf` (harder to analyze); deferred. -/
theorem correlationInfinite_neg_h_of_even_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (heven : Even A.card) :
    correlationInfinite G Λ (⟨J, -h, β⟩ : IsingParams ℝ) A
      = correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  unfold correlationInfinite
  refine iSup_congr ?_
  intro n
  rw [correlationAlongExhaustion_neg_h]
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  have h2k : (-1 : ℝ) ^ (k + k) = 1 := by
    rw [show k + k = 2 * k from by omega, pow_mul]
    simp
  rw [h2k, one_mul]

/-- **∞-volume `correlationInfinite` equals value at `|h|`**
(for even `|A|`): direct consequence of
`correlationInfinite_neg_h_of_even_card` via `abs_choice`. -/
theorem correlationInfinite_eq_abs_h_of_even_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (A : Finset V) (heven : Even A.card) :
    correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) A := by
  rcases abs_choice h with habs | habs
  · rw [habs]
  · rw [habs, correlationInfinite_neg_h_of_even_card G Λ J h β A heven]

/-- **Z₂ odd-symmetry for `magnetizationAlongExhaustion` under `h → -h`**:
at each stage `n`,
`magnetizationAlongExhaustion ⟨J,-h,β⟩ i n = -magnetizationAlongExhaustion ⟨J,h,β⟩ i n`.
Specialization of `correlationAlongExhaustion_neg_h` at `A = {i}`
(`|A| = 1`, `(-1)^1 = -1`). -/
theorem magnetizationAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  change correlationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) {i} n
    = -correlationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) {i} n
  rw [correlationAlongExhaustion_neg_h, Finset.card_singleton, pow_one]
  ring

/-- **Pointwise along-exhaustion `|M_along(h) n| = M_along(|h|) n`**
under ferromagnetism at `|h|` (`0 ≤ J`, `0 < β`). Along-exhaustion
counterpart of the Λ-layer `abs_magnetizationΛ_eq_magnetizationΛ_abs_h`
(PR #772); uses `magnetizationAlongExhaustion_nonneg` and
`magnetizationAlongExhaustion_neg_h` via `abs_choice`. -/
theorem abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) (n : ℕ) :
    |magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n|
      = magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n := by
  have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
    ⟨hJ, abs_nonneg _, hβ⟩
  have habs_nonneg :
      0 ≤ magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
    magnetizationAlongExhaustion_nonneg G Λ _ hf_abs i n
  rcases abs_choice h with habs | habs
  · -- |h| = h (h ≥ 0)
    have heq :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]
    rw [heq]
    apply abs_of_nonneg
    have h_ge : 0 ≤ h := by rw [← habs]; exact abs_nonneg h
    exact magnetizationAlongExhaustion_nonneg G Λ _ ⟨hJ, h_ge, hβ⟩ i n
  · -- |h| = -h (h ≤ 0)
    have hneg :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]; exact magnetizationAlongExhaustion_neg_h G Λ J h β i n
    rw [hneg]
    apply abs_of_nonpos
    have hne :
        0 ≤ -magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [← hneg]; exact habs_nonneg
    linarith

/-- **Along-exhaustion susceptibility under `h → -h`**:
`χ_along(⟨J, -h, β⟩; i, n) = χ_along(⟨J, h, β⟩; i, n) - 2·M_along(⟨J, h, β⟩; i, n)`.

Case split on `i ∈ Λ.volume n`:
- Covered stage: reduce to `susceptibilityΛ_neg_h` (PR #776) at the
  lifted subtype site via
  `susceptibilityAlongExhaustion_of_mem` and
  `magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ`.
- Uncovered stage: all three terms are `0`, so the identity is trivial.

Along-exhaustion counterpart of `susceptibilityΛ_neg_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          - 2 * magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi]
    exact susceptibilityΛ_neg_h G (Λ.volume n) J h β ⟨i, hi⟩
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi]
    ring

/-- **Along-exhaustion susceptibility at `|h|`** (capstone,
along-exhaustion layer, no ferromagnetic hypothesis):
`χ_along(⟨J, |h|, β⟩; i, n) = χ_along(⟨J, h, β⟩; i, n)
 + M_along(⟨J, |h|, β⟩; i, n) - M_along(⟨J, h, β⟩; i, n)`.

Case split on `i ∈ Λ.volume n`: covered stage reduces to
`susceptibilityΛ_eq_abs_h` (PR #776) at the lifted subtype site;
uncovered stage is trivial (all four terms `0`).

Along-exhaustion counterpart of PR #776's `susceptibilityΛ_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          + magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          - magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n := by
  by_cases hi : i ∈ Λ.volume n
  · rw [susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi,
        magnetizationAlongExhaustion_of_mem_eq_magnetizationΛ G Λ _ hi]
    exact susceptibilityΛ_eq_abs_h G (Λ.volume n) J h β ⟨i, hi⟩
  · rw [susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        susceptibilityAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi,
        magnetizationAlongExhaustion_of_not_mem G Λ _ hi]
    ring

/-- **Along-exhaustion pointwise `χ_along(h) ≤ χ_along(|h|)`** (A-4c)
under `0 ≤ J`, `0 < β`, at every stage `n` and any site `i : V`:
`χ_along(⟨J, h, β⟩; i, n) ≤ χ_along(⟨J, |h|, β⟩; i, n)`.

Proof by `abs_choice h`:
- `|h| = h` (`h ≥ 0`): the two sides are equal, so `≤` is reflexive.
- `|h| = -h` (`h ≤ 0`): starting from
  `susceptibilityAlongExhaustion_eq_abs_h` at `h`, we have
  `χ_along(|h|) = χ_along(h) + M_along(|h|) - M_along(h)`. Under
  ferromagnetism at `|h|` (i.e. `0 ≤ J, 0 ≤ |h|, 0 < β`, the first and
  last from hypotheses, the middle from `abs_nonneg`),
  `M_along(|h|) ≥ 0` by `magnetizationAlongExhaustion_nonneg`. Using
  `magnetizationAlongExhaustion_neg_h` at `|h| = -h` inverted:
  `M_along(h) = -M_along(|h|) ≤ 0`. Hence the correction
  `M_along(|h|) - M_along(h) = M_along(|h|) + |M_along(|h|)| ≥ 0`, so
  `χ_along(h) ≤ χ_along(|h|)`.

No ferromagnetic hypothesis at `h` is needed; only at `|h|`
(where it is automatic given `0 ≤ J, 0 < β`).

Prereq for the `BddAbove`-conditional ∞-volume lift A-5'
(`susceptibilityInfinite_le_abs_h`).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_le_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) (n : ℕ) :
    susceptibilityAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
      ≤ susceptibilityAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n := by
  rcases abs_choice h with habs | habs
  · -- |h| = h, equality of the two sides
    rw [habs]
  · -- |h| = -h, use the eq_abs_h + sign of M_along(h)
    have heq := susceptibilityAlongExhaustion_eq_abs_h G Λ J h β i n
    -- ferromagnetic at |h|
    have hf_abs : Ferromagnetic (⟨J, |h|, β⟩ : IsingParams ℝ) :=
      ⟨hJ, abs_nonneg _, hβ⟩
    -- M_along(|h|) ≥ 0
    have hM_abs_nonneg :
        0 ≤ magnetizationAlongExhaustion G Λ
              (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
      magnetizationAlongExhaustion_nonneg G Λ _ hf_abs i n
    -- M_along(|h|) = M_along(-h) = -M_along(h); hence M_along(h) ≤ 0
    have hM_neg :
        magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ
              (⟨J, h, β⟩ : IsingParams ℝ) i n := by
      rw [habs]; exact magnetizationAlongExhaustion_neg_h G Λ J h β i n
    have hM_h_nonpos :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n ≤ 0 :=
      by linarith
    linarith


end Ambient

end IsingModel
