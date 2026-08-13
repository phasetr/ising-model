import IsingModel.AmbientLatticeSum.TrivialSlices

/-!
# Bounds on the infinite-volume free energy, and its estimates at the zero field

`freeEnergyInfinite G Λ p` is the `Filter.limsup` along `atTop` of the stage sequence
`freeEnergyAlongExhaustion G Λ p`, whose value at a stage `n` is the free energy of the
subgraph of `G` induced by the finite volume `Λ.volume n`. The ambient graph
`G : SimpleGraph V` and the exhaustion `Λ : Exhaustion V` are arbitrary. Every statement
here takes `[DecidableEq V]`, `[Nonempty V]`, a stagewise `Fintype` instance on the edge set
of that induced subgraph — two of them in the single statement that carries two ambient
graphs — and a real `c` for which every stage with nonempty volume has at most `c` times as
many induced edges as vertices.

One group is stated at an arbitrary `p` under `Ferromagnetic p`, that is under `0 ≤ p.J`,
`0 ≤ p.h` and `0 < p.β`. It bounds the value from below by `log (2 * cosh (p.β * p.h))` and
by `log 2`, and, `log 2` being positive, states `0 < freeEnergyInfinite G Λ p` and
`0 ≤ freeEnergyInfinite G Λ p` outright. The same group compares two ambient graphs:
`G₁ ≤ G₂` gives `freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p`. That comparison is
the only statement in the module carrying two graphs, and so the only one taking two
stagewise `Fintype` instances; its edge-count hypothesis constrains the larger graph `G₂`
alone.

The other group is at the zero field, with the ferromagnetic hypothesis unbundled as
`0 ≤ J` and `0 < β`, and revolves around the two-sided estimate
`log 2 ≤ freeEnergyInfinite G Λ ⟨J, 0, β⟩ ≤ log 2 + β * J * c`. That estimate appears as a
conjunction on its own; extended by the two values `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`
and `freeEnergyInfinite G Λ ⟨J, 0, 0⟩ = log 2`; as the upper estimate
`freeEnergyInfinite G Λ ⟨J, 0, β⟩ - log 2 ≤ β * J * c` on the deviation from `log 2`, alone
and paired with `0 ≤ freeEnergyInfinite G Λ ⟨J, 0, β⟩ - log 2`; and as a bound by
`β * J * c` on the distance from `freeEnergyInfinite G Λ ⟨J, 0, β⟩` to each of those two
values, once with an absolute value around the difference and once without, each value on
its own and the two absolute-value forms together.
-/

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Uniform lower bound on `freeEnergyInfinite` under ferromagnetic**:
the per-stage bound `freeEnergyAlongExhaustion_ge_log_two_cosh` lifts to `limsup`:
`log(2·cosh(β·h)) ≤ freeEnergyInfinite G Λ p`.

Proof outline:
1. `Λ.exhaust {v}` gives eventual `(Λ.volume n).Nonempty`.
2. The ferromagnetic per-n lower bound
   `freeEnergyAlongExhaustion_ge_log_two_cosh` provides the
   `∀ᶠ`-form of the lower bound.
3. The `BoundedEdgeDensity`-based upper bound
   `freeEnergyAlongExhaustion_le_uniform_upper_bound` provides
   `IsBoundedUnder (· ≤ ·)` (needed by `le_limsup_of_frequently_le`).
4. `Filter.le_limsup_of_frequently_le` concludes. -/
theorem freeEnergyInfinite_ge_log_two_cosh
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite G Λ p := by
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hlower : ∀ᶠ n in Filter.atTop,
      Real.log (2 * Real.cosh (p.β * p.h))
        ≤ freeEnergyAlongExhaustion G Λ p n := by
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G Λ hf.hJ hf.hh hf.hβ n hne
  have hbdd_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ p) := by
    refine ⟨Real.log 2 + |p.β| * (|p.J| * c + |p.h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne
  exact Filter.le_limsup_of_frequently_le hlower.frequently hbdd_above

/-- **Corollary**: `log 2 ≤ freeEnergyInfinite G Λ p` under the same
hypotheses as `freeEnergyInfinite_ge_log_two_cosh`.

Follows from `cosh (β h) ≥ cosh 0 = 1` (`Real.one_le_cosh`), which
gives `2 · cosh (β h) ≥ 2` and hence
`log (2 · cosh (β h)) ≥ log 2`. -/
theorem freeEnergyInfinite_ge_log_two
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2 ≤ freeEnergyInfinite G Λ p := by
  have h_cosh_ge_one : (1 : ℝ) ≤ Real.cosh (p.β * p.h) :=
    Real.one_le_cosh _
  have h_le : Real.log 2 ≤ Real.log (2 * Real.cosh (p.β * p.h)) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    linarith
  exact h_le.trans
    (freeEnergyInfinite_ge_log_two_cosh G Λ p hf hc)

/-- **∞-vol sharper f sandwich at h = 0 under bounded edge density**:
under ferromagnetic `0 ≤ J, 0 < β` + bounded-edge-density witness `c`,
`log 2 ≤ freeEnergyInfinite G Λ ⟨J, 0, β⟩ ≤ log 2 + β·J·c`.

Combines `freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform` with
`freeEnergyInfinite_ge_log_two` (which is `log 2 ≤ f_∞` under
ferromagnetic + BED). The sandwich shows the ∞-vol free energy lies
in a tight `[log 2, log 2 + β·J·c]` interval — the lower bound is the
`J = 0` value and the upper bound is the edge-density-bounded
high-temperature contribution. -/
theorem freeEnergyInfinite_high_temp_h_zero_sandwich_exp_uniform
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2
      ≤ freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * c := by
  refine ⟨?_, freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    G Λ J β hJ hβ hc⟩
  exact freeEnergyInfinite_ge_log_two G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ⟨hJ, le_refl 0, hβ⟩ hc

/-- **∞-vol f complete-summary bundle at h = 0 under bounded edge
density**: under ferromagnetic `0 ≤ J, 0 < β` + bounded-edge-density
witness `c`, single statement bundling all known §18.3 ∞-vol
properties of `f` at `h = 0`:
  1. `log 2 ≤ freeEnergyInfinite G Λ ⟨J, 0, β⟩` (lower),
  2. `freeEnergyInfinite G Λ ⟨J, 0, β⟩ ≤ log 2 + β·J·c` (upper),
  3. `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2` (J = 0 trivial slice),
  4. `freeEnergyInfinite G Λ ⟨J, 0, 0⟩ = log 2` (β = 0 trivial slice).
Useful as a single import for downstream applications that need both
sandwich bounds and trivial-slice values at the infinite-volume level. -/
theorem freeEnergyInfinite_high_temp_h_zero_complete_summary_exp
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2
      ≤ freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * c ∧
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyInfinite G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  obtain ⟨h_lower, h_upper⟩ :=
    freeEnergyInfinite_high_temp_h_zero_sandwich_exp_uniform
      G Λ J β hJ hβ hc
  exact ⟨h_lower, h_upper,
    freeEnergyInfinite_zero_params_of_nonempty G Λ β,
    freeEnergyInfinite_beta_zero_of_nonempty G Λ J 0⟩

/-- **∞-vol f deviation bound from `log 2`**: under ferromagnetic
`0 ≤ J, 0 < β` + bounded-edge-density witness `c`,
`freeEnergyInfinite G Λ ⟨J, 0, β⟩ - log 2 ≤ β·J·c`.

Direct from `freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform`
by subtracting `log 2`. Useful as a pre-formed
"high-temperature deviation" estimate quantifying how much the ∞-vol
free energy can differ from its `J = 0` (free-spin) value `log 2`
under the linear-`β·J·c` regime.

In the `β·J → 0` limit, the RHS vanishes, recovering
`freeEnergyInfinite ⟨0, 0, β⟩ = log 2` continuously. -/
theorem freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * c := by
  have h_upper := freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    G Λ J β hJ hβ hc
  linarith

/-- **∞-vol f quantitative continuity at `J = 0`**: under ferromagnetic
`0 ≤ J, 0 < β` + bounded-edge-density witness `c`,
`|freeEnergyInfinite G Λ ⟨J, 0, β⟩ - freeEnergyInfinite G Λ ⟨0, 0, β⟩| ≤ β·J·c`.

Combines:
- `freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform`.
- Existing `freeEnergyInfinite_ge_log_two` lower `log 2 ≤ f_∞`.
- `freeEnergyInfinite_zero_params_of_nonempty` value `f_∞⟨0, 0, β⟩ = log 2`.

Right-continuity at `J = 0` with explicit linear modulus at the
infinite-volume level. -/
theorem freeEnergyInfinite_high_temp_h_zero_continuity_at_J_zero
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    |freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) -
        freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * c := by
  have hf0 : freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
    freeEnergyInfinite_zero_params_of_nonempty G Λ β
  rw [hf0]
  have h_upper := freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    G Λ J β hJ hβ hc
  have h_lower := freeEnergyInfinite_ge_log_two G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ⟨hJ, le_refl 0, hβ⟩ hc
  have h_dev_nn : (0 : ℝ) ≤ β * J * c := by
    have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
    -- We don't have 0 ≤ c direct here; derive from the upper bound
    -- via h_upper - log 2 ≤ β·J·c plus log 2 ≤ f_∞ (h_lower), so
    -- 0 ≤ f_∞ - log 2 ≤ β·J·c.
    linarith
  rw [abs_sub_le_iff]
  refine ⟨by linarith, by linarith⟩

/-- **∞-vol f quantitative continuity at `β = 0`**: under ferromagnetic
`0 ≤ J, 0 < β` + bounded-edge-density witness `c`,
`|freeEnergyInfinite G Λ ⟨J, 0, β⟩ - freeEnergyInfinite G Λ ⟨J, 0, 0⟩| ≤ β·J·c`.

Same bound as `freeEnergyInfinite_high_temp_h_zero_continuity_at_J_zero` since both
trivial slices give `f_∞ = log 2`. -/
theorem freeEnergyInfinite_high_temp_h_zero_continuity_at_beta_zero
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    |freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) -
        freeEnergyInfinite G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * c := by
  have hf0 : freeEnergyInfinite G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
    freeEnergyInfinite_beta_zero_of_nonempty G Λ J 0
  rw [hf0]
  have h_upper := freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    G Λ J β hJ hβ hc
  have h_lower := freeEnergyInfinite_ge_log_two G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ⟨hJ, le_refl 0, hβ⟩ hc
  rw [abs_sub_le_iff]
  refine ⟨by linarith, by linarith⟩

/-- **∞-vol f continuity bundle at trivial slices**: under ferromagnetic
`0 ≤ J, 0 < β` + bounded-edge-density witness `c`, single statement
bundling continuity at both `J = 0` and `β = 0` trivial slices. -/
theorem freeEnergyInfinite_high_temp_h_zero_continuity_bundle
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    |freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) -
        freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ)| ≤ β * J * c ∧
    |freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) -
        freeEnergyInfinite G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)| ≤ β * J * c :=
  ⟨freeEnergyInfinite_high_temp_h_zero_continuity_at_J_zero
      G Λ J β hJ hβ hc,
   freeEnergyInfinite_high_temp_h_zero_continuity_at_beta_zero
      G Λ J β hJ hβ hc⟩

/-- **∞-vol f deviation sandwich**: under ferromagnetic `0 ≤ J, 0 < β`
and bounded-edge-density witness `c`,
`0 ≤ freeEnergyInfinite G Λ ⟨J, 0, β⟩ - log 2 ≤ β·J·c`. -/
theorem freeEnergyInfinite_high_temp_h_zero_deviation_sandwich_exp
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * c := by
  have h_lower := freeEnergyInfinite_ge_log_two G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
    ⟨hJ, le_refl 0, hβ⟩ hc
  have h_upper := freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp
    G Λ J β hJ hβ hc
  exact ⟨by linarith, h_upper⟩

/-- **∞-vol f difference upper bound against the J=0 trivial slice
(GJ §18.3)**: under ferromagnetic + bounded-edge-density witness `c`,
`freeEnergyInfinite ⟨J, 0, β⟩ - freeEnergyInfinite ⟨0, 0, β⟩ ≤ β·J·c`.
The bounded quantity is the difference displayed above, not a ratio;
the `_ratio_bound` in the name does not describe the statement.

Reformulation of `freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp` using the
trivial-slice identity `f_∞⟨0, 0, β⟩ = log 2`. -/
theorem freeEnergyInfinite_high_temp_h_zero_ratio_bound
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * c := by
  rw [freeEnergyInfinite_zero_params_of_nonempty G Λ β]
  exact freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp
    G Λ J β hJ hβ hc

/-- **∞-vol f difference upper bound against the β=0 trivial slice**:
`freeEnergyInfinite ⟨J, 0, β⟩ - freeEnergyInfinite ⟨J, 0, 0⟩ ≤ β·J·c`.
As above, the bounded quantity is a difference, not a ratio. -/
theorem freeEnergyInfinite_high_temp_h_zero_ratio_bound_beta_zero
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyInfinite G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * c := by
  rw [freeEnergyInfinite_beta_zero_of_nonempty G Λ J 0]
  exact freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp
    G Λ J β hJ hβ hc

/-- **Strict positivity** of `freeEnergyInfinite` under the standard
ferromagnetic + `BoundedEdgeDensity` + `[Nonempty V]` setup:
`0 < freeEnergyInfinite G Λ p`.

Follows from `freeEnergyInfinite_ge_log_two` together with
`Real.log_pos` at `2 > 1`. -/
theorem freeEnergyInfinite_pos
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite G Λ p :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    (freeEnergyInfinite_ge_log_two G Λ p hf hc)

/-- **Nonnegativity** of `freeEnergyInfinite` under the standard
hypotheses. Immediate from strict positivity. -/
theorem freeEnergyInfinite_nonneg
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite G Λ p :=
  (freeEnergyInfinite_pos G Λ p hf hc).le

set_option linter.unusedFintypeInType false in
/-- **`freeEnergyInfinite` is monotone in the ambient subgraph**:
for `G₁ ≤ G₂` and ferromagnetic `p`,
`freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p`
(under suitable boundedness hypotheses used internally to control
the `limsup`).

Proof: apply `Filter.limsup_le_limsup` to the per-n
`freeEnergyAlongExhaustion_monotone_ambient_subgraph`. The
`IsCoboundedUnder` side is discharged via the ferromagnetic lower
bound `freeEnergyAlongExhaustion_ge_log_two_cosh`; the
`IsBoundedUnder` side via the `BoundedEdgeDensity`-driven upper
bound `freeEnergyAlongExhaustion_le_uniform_upper_bound`. -/
theorem freeEnergyInfinite_monotone_ambient_subgraph
    [Nonempty V] {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂)
    (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G₂ (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p := by
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G₁ Λ p n
        ≤ freeEnergyAlongExhaustion G₂ Λ p n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_ambient_subgraph h Λ p hf n
  have hbdd_below_G₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G₁ Λ p) := by
    refine ⟨Real.log (2 * Real.cosh (p.β * p.h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G₁ Λ hf.hJ hf.hh hf.hβ n hne
  have hbdd_above_G₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G₂ Λ p) := by
    refine ⟨Real.log 2 + |p.β| * (|p.J| * c + |p.h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G₂ Λ p hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_G₁.isCoboundedUnder_le hbdd_above_G₂

end Ambient

end IsingModel
