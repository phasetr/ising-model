import IsingModel.AmbientLattice.MagnetizationInfinite.Basic

/-!
# Infinite-volume magnetization h-symmetry bounds

One-sided absolute-field and nonpositive-field wrappers for
`magnetizationInfinite`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-! ## Moved: Λ-level h-symmetry / J_zero / tanh-power wrappers

The 10 Λ-level h-symmetry, odd-vanish at h=0, J_zero, and tanh-power
lower-bound wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion / correlationInfinite h-symmetry wrappers

The 9 alongExhaustion / correlationInfinite h-symmetry wrappers now
live in
`IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: susceptibilityInfinite definition + 4 wrappers

The infinite-volume susceptibility definition `susceptibilityInfinite`
and 4 of its properties now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibility`.
The earlier import path is preserved by re-importing the new child.
The h-symmetry bound `abs_magnetizationInfinite_le_magnetizationInfinite_abs_h`
remains here because it directly references `magnetizationInfinite`.
-/

/-- **∞-volume one-sided `|M_∞(h)| ≤ M_∞(|h|)`** under ferromagnetism
at `|h|` (`0 ≤ J`, `0 < β`).

**Inequality rather than equality**: the natural equality
`|M_∞(h)| = M_∞(|h|)` (true in Glimm–Jaffe §5.3's standard
thermodynamic limit) **does not hold in general** under this repo's
sup-based `magnetizationInfinite := ⨆ n, magnetizationAlongExhaustion
…`. Concretely: at `h < 0` ferromagnetic, each covered stage gives
`M_along(n) ≤ 0` by `magnetizationAlongExhaustion_neg_h` plus
ferromagnetic nonnegativity at `|h|`; any stage with `i ∉ Λ.volume n`
contributes the forced value `0` (by the
`if A ⊆ Λ.volume n then … else 0` convention). Thus if there is even
one such "missed stage", `M_∞(h) = 0` while `M_∞(|h|) > 0`, breaking
equality. Since `Exhaustion` does not require a missed stage, this
is an obstruction/example rather than a universal consequence of
`h < 0` ferromagnetic alone — but it shows the equality cannot be
expected to hold in general. This is the same odd-`|A|` obstruction
already noted in `correlationInfinite_neg_h_of_even_card`.

The one-sided bound still holds unconditionally: at each stage
`|M_along(h) n| = M_along(|h|) n ≥ 0`, so both
`M_∞(h) ≤ M_∞(|h|)` (pointwise `f ≤ |f| = g`) and
`-M_∞(|h|) ≤ M_∞(h)` (via `a(0) ≤ ciSup a` and
`-|f(0)| ≤ f(0) ≤ ciSup f`).

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background).  Part of the
§5.3 Z₂ h-symmetry series tracked in issue #770. -/
theorem abs_magnetizationInfinite_le_magnetizationInfinite_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : V) :
    |magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i|
      ≤ magnetizationInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i := by
  rw [magnetizationInfinite_eq_ciSup, magnetizationInfinite_eq_ciSup]
  set f : ℕ → ℝ :=
    fun n => magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
    with hf_def
  set a : ℕ → ℝ :=
    fun n => magnetizationAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) i n
    with ha_def
  have habs : ∀ n, |f n| = a n := fun n =>
    abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
      G Λ J h β hJ hβ i n
  have hf_bdd : BddAbove (Set.range f) :=
    correlationAlongExhaustion_bddAbove G Λ (⟨J, h, β⟩ : IsingParams ℝ) {i}
  have ha_bdd : BddAbove (Set.range a) :=
    correlationAlongExhaustion_bddAbove G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) {i}
  apply abs_le.mpr
  refine ⟨?_, ?_⟩
  · -- -⨆ a ≤ ⨆ f : pick n = 0 as witness
    have h1 : a 0 ≤ ⨆ n, a n := le_ciSup ha_bdd 0
    have h2 : -|f 0| ≤ f 0 := neg_abs_le _
    have h3 : f 0 ≤ ⨆ n, f n := le_ciSup hf_bdd 0
    have habs0 : |f 0| = a 0 := habs 0
    linarith
  · -- ⨆ f ≤ ⨆ a : pointwise f n ≤ |f n| = a n ≤ ⨆ a
    apply ciSup_le
    intro n
    calc f n ≤ |f n| := le_abs_self _
      _ = a n := habs n
      _ ≤ ⨆ n, a n := le_ciSup ha_bdd n

/-- **`magnetizationInfinite ≤ 0` at `h ≤ 0` under ferromagnetism**:
for `0 ≤ J`, `0 < β`, `h ≤ 0`, any exhaustion `Λ`, and any ambient
site `i`, `magnetizationInfinite G Λ ⟨J, h, β⟩ i ≤ 0`.

Sign-control companion to `magnetizationInfinite_nonneg` (which covers
the `h ≥ 0` side under ferromagnetism). Proof: rewrite `M_∞` as
`⨆ n, M_along n`, then show each stage value is `≤ 0`:

- covered stages (`i ∈ Λ.volume n`): `magnetizationAlongExhaustion_neg_h`
  rewrites `M_along ⟨J, h, β⟩ = -M_along ⟨J, -h, β⟩`, and
  `magnetizationAlongExhaustion_nonneg` at `⟨J, -h, β⟩` (ferromagnetic,
  since `0 ≤ -h`) gives `0 ≤ M_along ⟨J, -h, β⟩`, hence
  `M_along ⟨J, h, β⟩ ≤ 0`;
- uncovered stages (`i ∉ Λ.volume n`): `M_along = 0 ≤ 0`.

Close with `ciSup_le`.

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background). Part of the §5.3
Z₂ h-symmetry series tracked in issue #770. -/
theorem magnetizationInfinite_nonpos_of_nonpos_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0) (i : V) :
    magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 := by
  rw [magnetizationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hi : i ∈ Λ.volume n
  · have hneg :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n
          = -magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n := by
      have := magnetizationAlongExhaustion_neg_h G Λ J (-h) β i n
      simpa using this
    rw [hneg]
    have hnonneg :
        0 ≤ magnetizationAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) i n :=
      magnetizationAlongExhaustion_nonneg G Λ _
        ⟨hJ, by linarith, hβ⟩ i n
    linarith
  · rw [magnetizationAlongExhaustion_of_not_mem G Λ _ hi]

/-- **`magnetizationInfinite = 0` at `h ≤ 0` when some stage misses `i`**:
under ferromagnetism at `|h|` (`0 ≤ J`, `0 < β`) and `h ≤ 0`, if there
exists a stage `n₀` with `i ∉ Λ.volume n₀`, then
`magnetizationInfinite G Λ ⟨J, h, β⟩ i = 0`.

Concretizes the obstruction noted in
`abs_magnetizationInfinite_le_magnetizationInfinite_abs_h`: at `h ≤ 0`,
missed stages contribute the forced value `0` and dominate the sup.

Proof: `magnetizationInfinite_nonpos_of_nonpos_h` gives the `≤ 0`
direction; for `0 ≤ M_∞`, the missed stage has
`M_along n₀ = 0 ≤ M_∞` via
`magnetizationAlongExhaustion_le_magnetizationInfinite`. Close with
`le_antisymm`.

Reference: Glimm–Jaffe §5.3 pp. 77–80 (background). Part of the §5.3
Z₂ h-symmetry series tracked in issue #770. -/
theorem magnetizationInfinite_eq_zero_of_exists_stage_not_mem
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0) (i : V)
    (hmiss : ∃ n, i ∉ Λ.volume n) :
    magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i = 0 := by
  obtain ⟨n₀, hn₀⟩ := hmiss
  have hupper :
      magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 :=
    magnetizationInfinite_nonpos_of_nonpos_h G Λ J h β hJ hβ hh i
  have hlower :
      0 ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i := by
    have hzero :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n₀ = 0 :=
      magnetizationAlongExhaustion_of_not_mem G Λ _ hn₀
    have :
        magnetizationAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) i n₀
          ≤ magnetizationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) i :=
      magnetizationAlongExhaustion_le_magnetizationInfinite G Λ _ i n₀
    linarith
  linarith

end Ambient
end IsingModel
