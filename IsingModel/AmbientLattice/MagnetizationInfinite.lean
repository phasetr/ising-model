import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibility
import IsingModel.AmbientLattice.MagnetizationInfiniteHZeroJZero
import IsingModel.AmbientLattice.MagnetizationInfiniteEmptyTrivial
import IsingModel.AmbientLattice.MagnetizationInfiniteMagTrivial
import IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibilityRegularity

/-!
# Infinite-volume single-site magnetization

Definition and properties of `magnetizationInfinite` (the thermodynamic
limit of the per-site magnetization) and related objects.

Includes: monotonicity in `h`, `β`, `J`; h-symmetry; spontaneous
magnetization limit; susceptibilityInfinite; and various special cases.

## References

* Glimm–Jaffe, *Quantum Physics*, §4.2–4.4, §5.3.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Infinite-volume single-site magnetization

Specialize `correlationInfinite` to single sites `A = {i}` to obtain
the formal thermodynamic-limit magnetization `magnetizationInfinite`.
All basic properties follow directly from the general
`correlationInfinite` API (PR #91–#97).

Reference: Glimm–Jaffe §4.2 (pp. 57ff) / §5.1 (p. 77, $m^* := \lim_{h \to 0^+} M$). -/

/-- **Infinite-volume single-site magnetization**: for a ferromagnetic
Ising model on an ambient type `V`, exhaustion `Λ`, and site `i : V`,
`magnetizationInfinite G Λ p i := correlationInfinite G Λ p {i}`.

This is the formal thermodynamic-limit magnetization
$\langle \sigma_i \rangle_\infty^{\mathrm{FM}}$. -/
noncomputable def magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) : ℝ :=
  correlationInfinite G Λ p {i}

/-- **Unfolding of `magnetizationInfinite`**:
`magnetizationInfinite G Λ p i = correlationInfinite G Λ p {i}`,
by definition. -/
theorem magnetizationInfinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i = correlationInfinite G Λ p {i} := rfl

/-- **Nonnegativity of `magnetizationInfinite`** (ferromagnetic):
`0 ≤ magnetizationInfinite G Λ p i`.  Specialization of
`correlationInfinite_nonneg` at `A = {i}`. -/
theorem magnetizationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    0 ≤ magnetizationInfinite G Λ p i :=
  correlationInfinite_nonneg G Λ p hf {i}

/-- **Upper bound**: `magnetizationInfinite G Λ p i ≤ 1`. Specialization
of `correlationInfinite_le_one`. -/
theorem magnetizationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i ≤ 1 :=
  correlationInfinite_le_one G Λ p {i}

/-- **Magnetization ∞-volume ambient-subgraph monotonicity**:
for `G₁ ≤ G₂` and ferromagnetic `p`. Specialization of
`correlationInfinite_monotone_ambient_subgraph` at `A = {i}`. -/
theorem magnetizationInfinite_monotone_ambient_subgraph
    {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    magnetizationInfinite G₁ Λ p i ≤ magnetizationInfinite G₂ Λ p i :=
  correlationInfinite_monotone_ambient_subgraph h Λ p hf {i}

/-- **`|magnetizationInfinite| ≤ 1`** unconditionally (any parameters).
Direct specialization of `abs_correlationInfinite_le_one` at `A = {i}`. -/
theorem abs_magnetizationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    |magnetizationInfinite G Λ p i| ≤ 1 :=
  abs_correlationInfinite_le_one G Λ p {i}

/-- **`-1 ≤ magnetizationInfinite`** unconditionally. -/
theorem neg_one_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    -1 ≤ magnetizationInfinite G Λ p i :=
  neg_one_le_correlationInfinite G Λ p {i}

/-- **`magnetizationInfinite² ≤ 1`** unconditionally. From
`abs_magnetizationInfinite_le_one` via `sq_le_one'`. -/
theorem magnetizationInfinite_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i ^ 2 ≤ 1 := by
  have h := abs_magnetizationInfinite_le_one G Λ p i
  have : |magnetizationInfinite G Λ p i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Convergence of `magnetizationAlongExhaustion` to `magnetizationInfinite`**
for ferromagnetic `p`:
`Tendsto (magnetizationAlongExhaustion G Λ p i) atTop (nhds (magnetizationInfinite G Λ p i))`.
Direct specialization of `tendsto_correlationAlongExhaustion_correlationInfinite`
at `A = {i}`, unfolding `magnetizationInfinite := correlationInfinite … {i}`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds (magnetizationInfinite G Λ p i)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}

/-- **Existential convergence of `magnetizationAlongExhaustion`** for
ferromagnetic `p`: `∃ L, Tendsto (magnetizationAlongExhaustion G Λ p i) atTop (nhds L)`.
Specialization of `correlationAlongExhaustion_convergent` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_convergent
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    ∃ L : ℝ, Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds L) :=
  correlationAlongExhaustion_convergent G Λ p hf {i}

/-- **Stage-index monotonicity of `magnetizationAlongExhaustion`** for
ferromagnetic `p`. Specialization of `correlationAlongExhaustion_monotone`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Monotone (magnetizationAlongExhaustion G Λ p i) :=
  correlationAlongExhaustion_monotone G Λ p hf {i}

/-- **`magnetizationAlongExhaustion` is bounded above** (unconditional):
the range of `n ↦ magnetizationAlongExhaustion G Λ p i n` is
bounded above. Specialization of `correlationAlongExhaustion_bddAbove`
at `A = {i}`. -/
theorem magnetizationAlongExhaustion_bddAbove
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    BddAbove (Set.range (magnetizationAlongExhaustion G Λ p i)) :=
  correlationAlongExhaustion_bddAbove G Λ p {i}

/-- **`magnetizationAlongExhaustion` is bounded below** (unconditional):
specialization of `correlationAlongExhaustion_bddBelow` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_bddBelow
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    BddBelow (Set.range (magnetizationAlongExhaustion G Λ p i)) :=
  correlationAlongExhaustion_bddBelow G Λ p {i}

/-- **Convergence to the supremum** for `magnetizationAlongExhaustion`
(ferromagnetic): `Tendsto … atTop (nhds (⨆ n, magnetizationAlongExhaustion G Λ p i n))`.
Specialization of `correlationAlongExhaustion_tendsto_ciSup` at
`A = {i}`. -/
theorem magnetizationAlongExhaustion_tendsto_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    Filter.Tendsto (magnetizationAlongExhaustion G Λ p i)
      Filter.atTop (nhds (⨆ n, magnetizationAlongExhaustion G Λ p i n)) :=
  correlationAlongExhaustion_tendsto_ciSup G Λ p hf {i}

/-- **`magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite G Λ p i = ⨆ n, magnetizationAlongExhaustion G Λ p i n`.
Definitional identity threading `magnetizationInfinite := correlationInfinite … {i}`
and `correlationInfinite := ⨆ n, correlationAlongExhaustion …` through
`magnetizationAlongExhaustion := correlationAlongExhaustion … {i}`. -/
theorem magnetizationInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) :
    magnetizationInfinite G Λ p i
      = ⨆ n, magnetizationAlongExhaustion G Λ p i n := rfl

/-- **Pointwise bound**: `magnetizationAlongExhaustion G Λ p i n ≤
magnetizationInfinite G Λ p i` at every `n`. Specialization at `A = {i}`. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ p i n ≤ magnetizationInfinite G Λ p i :=
  correlationAlongExhaustion_le_correlationInfinite G Λ p {i} n

/-- **Exhaustion-independence of `magnetizationInfinite`**:
the value does not depend on the choice of exhaustion.  Specialization
of `correlationInfinite_indep_exhaustion`. -/
theorem magnetizationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : V) :
    magnetizationInfinite G Λ p i = magnetizationInfinite G Λ' p i :=
  correlationInfinite_indep_exhaustion G Λ Λ' p hf {i}

/-- **J-direction monotonicity of `magnetizationInfinite`** (for
fixed `h ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_J`. -/
theorem magnetizationInfinite_monotone_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J G Λ hh hβ {i}

/-- **h-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, β > 0`).  Specialization of
`correlationInfinite_monotone_h`. -/
theorem magnetizationInfinite_monotone_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : V) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h G Λ hJ hβ {i}

/-- **β-direction monotonicity of `magnetizationInfinite`** (for
fixed `J ≥ 0, h ≥ 0`).  Specialization of
`correlationInfinite_monotone_beta`. -/
theorem magnetizationInfinite_monotone_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : V) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta G Λ hJ hh {i}


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



/-! ## Moved: susceptibilityInfinite J = 0 closed form + regularity at J = 0

The 7 susceptibilityInfinite J = 0 closed form + trivial-slice +
regularity-at-J=0 wrappers now live in
`IsingModel.AmbientLattice.MagnetizationInfiniteSusceptibilityRegularity`.
The earlier import path is preserved by re-importing the new child.
-/

/-- **`magnetizationInfinite` ContinuousOn h on Ici 0 at J = 0** (Step 266):
For `0 < β`, `h ↦ magnetizationInfinite ⟨0, h, β⟩ i = tanh(β·h)` (Step 233's
`magnetizationInfinite_J_zero`), which is continuous. -/
theorem magnetizationInfinite_continuousOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    ContinuousOn
      (fun h => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici (0 : ℝ)) := by
  have hF_eq : ∀ h ∈ Set.Ici (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro h hh_in
    have hh_nn : 0 ≤ h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont : Continuous (fun h : ℝ => Real.tanh (β * h)) :=
    h_tanh_cont.comp (continuous_const.mul continuous_id)
  exact h_cont.continuousOn.congr (fun h hh_in => hF_eq h hh_in)

/-- **`magnetizationInfinite` ContinuousOn β on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_continuousOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    ContinuousOn
      (fun β => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_cont : Continuous (fun β : ℝ => Real.tanh (β * h)) :=
    h_tanh_cont.comp (continuous_id.mul continuous_const)
  exact h_cont.continuousOn.congr (fun β hβ_in => hF_eq β hβ_in)

/-- **`magnetizationInfinite` DifferentiableOn h on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_differentiableOn_field_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hβ : 0 < β) (i : V) :
    DifferentiableOn ℝ
      (fun h => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ h ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro h hh_in
    have hh_pos : 0 < h := hh_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_pos.le, hβ⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff : Differentiable ℝ (fun h : ℝ => Real.tanh (β * h)) :=
    h_tanh_diff.comp ((differentiable_const _).mul differentiable_id)
  exact h_diff.differentiableOn.congr (fun h hh_in => hF_eq h hh_in)

/-- **`magnetizationInfinite` DifferentiableOn β on Ioi 0 at J = 0** (Step 266). -/
theorem magnetizationInfinite_differentiableOn_beta_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh_nn : 0 ≤ h) (i : V) :
    DifferentiableOn ℝ
      (fun β => magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi (0 : ℝ)) := by
  have hF_eq : ∀ β ∈ Set.Ioi (0 : ℝ),
      magnetizationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) := by
    intro β hβ_in
    have hβ_pos : 0 < β := hβ_in
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_nn, hβ_pos⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tanh_diff : Differentiable ℝ (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh (fun x => (Real.cosh_pos x).ne')
  have h_diff : Differentiable ℝ (fun β : ℝ => Real.tanh (β * h)) :=
    h_tanh_diff.comp (differentiable_id.mul (differentiable_const _))
  exact h_diff.differentiableOn.congr (fun β hβ_in => hF_eq β hβ_in)


end Ambient
end IsingModel
