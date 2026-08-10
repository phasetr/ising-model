import IsingModel.AmbientLatticeSum.SuperadditiveConvergence

/-!
# The free energy on the slices where a parameter vanishes, and Fekete convergence there

For an arbitrary ambient graph `G : SimpleGraph V` and an arbitrary exhaustion
`Λ : Exhaustion V`, `freeEnergyAlongExhaustion G Λ p` reads at a stage `n` the free energy of
the subgraph of `G` induced by `Λ.volume n`, and `freeEnergyInfinite G Λ p` is its
`Filter.limsup` along `atTop`. Nothing in this module assumes `Ferromagnetic p` or any sign
condition on `p.J`, `p.h` or `p.β`: the slices below are exact parameter values, not
inequalities.

At `J = h = 0` the logarithm of the partition function on a finite volume `Λ : Finset V` has
the closed form `↑Λ.card * log 2`, asking nothing of `Λ` beyond the `Fintype` instance on
the edge set it induces — in particular not that it be nonempty.

`DisjointTowerHypotheses` is built here in three ways. Given a real `c` with
`log (partitionFunctionΛ G (Λ.volume n) p) = ↑(Λ.volume n).card * c` at every stage, the
super-additivity field follows from additivity of the stage cardinalities alone, so beyond
that closed form the builder asks only for that additivity and for `(Λ.volume 1).card ≠ 0`.
The slices `J = 0` and `β = 0` are instances of it, the constant coming from the closed forms
`log (partitionFunctionΛ G Λ ⟨0, h, β⟩) = ↑Λ.card * log (2 * cosh (β * h))` and
`log (partitionFunctionΛ G Λ ⟨J, h, 0⟩) = ↑Λ.card * log 2`. Feeding those records into the
convergence statement gives, on each of the two slices, convergence of the stage sequence to
the `freeEnergyInfinite` at those same parameters, out of `BoundedEdgeDensity G Λ`,
cardinality additivity and a non-degenerate first stage.

A second route to the same slices runs through eventual constancy: a stage sequence
eventually equal to a real `c` tends to `c`, and then `freeEnergyInfinite` is `c`. Under the
hypothesis that the stage volumes are eventually nonempty this yields
`freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`, `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2` and
`freeEnergyInfinite G Λ ⟨0, h, β⟩ = log (2 * cosh (β * h))`, together with a `Filter.Tendsto`
companion for the stage sequence on each of those three slices. The three
`freeEnergyInfinite` equations are restated once more with the eventual hypothesis discharged
by `[Nonempty V]`; those restatements are the only statements in the module taking
`[Nonempty V]`.

At `J = 0` the value does not see the ambient graph at all:
`freeEnergyInfinite G Λ ⟨0, h, β⟩` equals `freeEnergyInfinite ⊥ Λ ⟨0, h, β⟩`. That is the
only statement here naming two graphs, and so the only one taking two stagewise `Fintype`
instances.
-/

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Closed form for `log (partitionFunctionΛ G Λ ⟨0, 0, β⟩)`**:
at `J = h = 0`, `log Z_Λ = |Λ| · log 2`. Direct from
`IsingModel.partitionFunction_zero_params`
(`Z = Fintype.card (Config ↑Λ) = 2^|↑Λ|`) via
`card_config_eq_two_pow`, `Real.log_pow`, and `Fintype.card_coe`. -/
theorem log_partitionFunctionΛ_zero_params
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Real.log (partitionFunctionΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2 := by
  change Real.log (IsingModel.partitionFunction
      (inducedGraph G Λ) (⟨0, 0, β⟩ : IsingParams ℝ)) = _
  rw [IsingModel.partitionFunction_zero_params,
      IsingModel.card_config_eq_two_pow]
  push_cast
  rw [Real.log_pow, Fintype.card_coe]

/-- **Generic `DisjointTowerHypotheses` builder from log-linear `log Z`**
(GJ §4.6 Prop 4.6.1 helper): whenever
`log Z_{Λ_n} = |Λ_n| · c` for all `n` with some fixed constant `c`
(e.g. `J = 0` gives `c = log(2·cosh(β·h))`; `β = 0` gives `c = log 2`),
the super-additivity requirement of `DisjointTowerHypotheses` is
discharged automatically under `hcard_add`, and
`hcard_add` + `hcard_one` suffice to build the record.

Mathematical content: the super-additivity hypothesis reduces to
`(|Λ_m| + |Λ_n|) · c ≤ |Λ_{m+n}| · c`, which holds with equality
under `hcard_add`. -/
def DisjointTowerHypotheses.of_log_linear_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (c : ℝ)
    (hlog : ∀ n, Real.log (partitionFunctionΛ G (Λ.volume n) p)
                  = ((Λ.volume n).card : ℝ) * c)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    DisjointTowerHypotheses G Λ p where
  card_add := hcard_add
  super := by
    intro m n
    rw [hlog, hlog, hlog]
    have hcast : ((Λ.volume (m + n)).card : ℝ)
        = ((Λ.volume m).card : ℝ) + ((Λ.volume n).card : ℝ) := by
      exact_mod_cast hcard_add m n
    rw [hcast]
    ring_nf
    exact le_refl _
  card_one := hcard_one

/-- **Concrete `DisjointTowerHypotheses` instance at `J = 0`**
(GJ §4.6 Prop 4.6.1, p. 68): given `hcard_add` (cardinality additive
exhaustion) and `hcard_one` (non-degenerate base step) as inputs, the
remaining super-additivity field of `DisjointTowerHypotheses` at
`J = 0` is discharged automatically via
`DisjointTowerHypotheses.of_log_linear_card` with
`c = log(2·cosh(β·h))` — no translation invariance needed. -/
def DisjointTowerHypotheses.of_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    DisjointTowerHypotheses G Λ (⟨0, h, β⟩ : IsingParams ℝ) :=
  DisjointTowerHypotheses.of_log_linear_card G Λ
    (⟨0, h, β⟩ : IsingParams ℝ) (Real.log (2 * Real.cosh (β * h)))
    (fun n => log_partitionFunctionΛ_J_zero G (Λ.volume n) h β)
    hcard_add hcard_one

/-- **Concrete `DisjointTowerHypotheses` instance at `β = 0`**
(GJ §4.6 Prop 4.6.1, p. 68): given `hcard_add` (cardinality additive
exhaustion) and `hcard_one` (non-degenerate base step) as inputs, the
remaining super-additivity field of `DisjointTowerHypotheses` at
`β = 0` is discharged automatically via
`DisjointTowerHypotheses.of_log_linear_card` with `c = log 2` —
no translation invariance needed. -/
def DisjointTowerHypotheses.of_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    DisjointTowerHypotheses G Λ (⟨J, h, 0⟩ : IsingParams ℝ) :=
  DisjointTowerHypotheses.of_log_linear_card G Λ
    (⟨J, h, 0⟩ : IsingParams ℝ) (Real.log 2)
    (fun n => log_partitionFunctionΛ_beta_zero G (Λ.volume n) J h)
    hcard_add hcard_one

/-- **Fekete convergence of `freeEnergyAlongExhaustion` at `J = 0`**
(GJ §4.6 Prop 4.6.1, p. 68, concrete `J = 0` instance).

Given a cardinality-additive exhaustion with non-degenerate base step
and bounded edge density, the free-energy density sequence
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n`
converges to `freeEnergyInfinite G Λ ⟨0, h, β⟩`.

This is the first concrete corollary of
`freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses`,
combining `DisjointTowerHypotheses.of_J_zero` (automatic
super-additivity at `J = 0`) with `BoundedEdgeDensity`.

Note: the limit coincides with `log(2 · cosh(β · h))` (from
`freeEnergyAlongExhaustion_J_zero`) on nonempty stages, so this is a
more explicit version of
`freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty`
obtained via the Fekete pipeline rather than the
eventually-constant shortcut. -/
theorem freeEnergyAlongExhaustion_J_zero_tendsto_of_hcard_add
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G Λ _
    hBED (DisjointTowerHypotheses.of_J_zero G Λ h β hcard_add hcard_one)

/-- **Fekete convergence of `freeEnergyAlongExhaustion` at `β = 0`**
(GJ §4.6 Prop 4.6.1, p. 68, concrete `β = 0` instance).

Given a cardinality-additive exhaustion with non-degenerate base step
and bounded edge density, the free-energy density sequence
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n` converges to
`freeEnergyInfinite G Λ ⟨J, h, 0⟩`.

Combines `DisjointTowerHypotheses.of_beta_zero` (automatic
super-additivity at `β = 0` via the log-linear-card builder) with
`BoundedEdgeDensity`. Parallel to the `J = 0` instance
`freeEnergyAlongExhaustion_J_zero_tendsto_of_hcard_add`. -/
theorem freeEnergyAlongExhaustion_beta_zero_tendsto_of_hcard_add
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses G Λ _
    hBED (DisjointTowerHypotheses.of_beta_zero G Λ J h hcard_add hcard_one)

/-- **Eventually constant ⇒ `freeEnergyInfinite` equals the constant.**

If `∀ᶠ n in atTop, freeEnergyAlongExhaustion G Λ p n = c`, then
`freeEnergyInfinite G Λ p = c`. Direct corollary of
`freeEnergyInfinite_eq_of_tendsto`: an eventually-constant sequence
tends to that constant (`Filter.tendsto_const_nhds` via
`Filter.Tendsto.congr'`).

Generalization of the argument in `freeEnergyInfinite_beta_zero` /
`_zero_params` which handle the always-constant (all-stages-nonempty)
case. -/
theorem freeEnergyInfinite_of_eventually_const
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion G Λ p n = c) :
    freeEnergyInfinite G Λ p = c := by
  refine freeEnergyInfinite_eq_of_tendsto G Λ p ?_
  exact tendsto_const_nhds.congr' (h.mono (fun _ hn => hn.symm))

/-- **β=0 infinite-volume closed form, weakened eventual form**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒ freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`.

Weakening of `freeEnergyInfinite_beta_zero` (`∀ n` → `∀ᶠ n`).
The eventual hypothesis is automatic under `[Infinite V]` via
`Exhaustion.eventually_volume_nonempty`.

Uses `freeEnergyInfinite_of_eventually_const` with the per-stage
`freeEnergyAlongExhaustion_beta_zero`. -/
theorem freeEnergyInfinite_beta_zero_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_beta_zero G Λ J h n hn

/-- **J=h=0 infinite-volume closed form, weakened eventual form**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒ freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`.

Weakening of `freeEnergyInfinite_zero_params` (`∀ n` → `∀ᶠ n`). -/
theorem freeEnergyInfinite_zero_params_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_zero_params G Λ β n hn

/-- **J=0 infinite-volume closed form (graph-independent)**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒
 freeEnergyInfinite G Λ ⟨0, h, β⟩ = log (2·cosh(β·h))`.

Graph independence: since the interaction term vanishes at `J = 0`,
the `freeEnergy` agrees with that of the `⊥` graph at each stage.
Direct application of `freeEnergyInfinite_of_eventually_const` with
the stagewise `freeEnergyAlongExhaustion_J_zero`. -/
theorem freeEnergyInfinite_J_zero_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_J_zero G Λ h β n hn

/-- **Generic Tendsto helper**: if the stagewise `freeEnergyAlongExhaustion`
sequence is eventually equal to `c`, then it tends to `c`. Factors the
`tendsto_const_nhds.congr'` + `filter_upwards` pattern out of the
specific `_J_zero` / `_beta_zero` / `_zero_params` Tendsto lemmas. -/
theorem freeEnergyAlongExhaustion_tendsto_of_eventually_const
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion G Λ p n = c) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds c) :=
  tendsto_const_nhds.congr' (h.mono (fun _ hn => hn.symm))

/-- **`freeEnergyAlongExhaustion` at J=0 converges (Tendsto form)**:
assuming eventually `(Λ.volume n).Nonempty`, the sequence
`n ↦ freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n` tends to
`log(2·cosh(β·h))` in the topology on `ℝ`.

First non-trivial ∞-volume convergence under the scope update
(CLAUDE.local.md: infinite-volume systems are in scope). The J=0 slice sidesteps the
translation-invariance issue of the general Fekete program because
the stagewise sequence is eventually constant (PR #174
`freeEnergyAlongExhaustion_J_zero`); then via
`freeEnergyAlongExhaustion_tendsto_of_eventually_const`. -/
theorem freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_J_zero G Λ h β n hn

/-- **β=0 slice ∞-vol Tendsto**: `∀ᶠ n, (Λ.volume n).Nonempty ⇒
Tendsto (freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩) atTop (𝓝 (log 2))`.

Companion to `_J_zero_tendsto_of_eventually_nonempty` (PR #178):
at β=0 the stagewise sequence is eventually constantly `log 2`
(PR #132 `freeEnergyAlongExhaustion_beta_zero`). -/
theorem freeEnergyAlongExhaustion_beta_zero_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_beta_zero G Λ J h n hn

/-- **J=h=0 slice ∞-vol Tendsto**: `∀ᶠ n, (Λ.volume n).Nonempty ⇒
Tendsto (freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩) atTop (𝓝 (log 2))`.

Companion to `_J_zero_tendsto_of_eventually_nonempty` (PR #178):
at J=h=0 the stagewise sequence is eventually constantly `log 2`
(`freeEnergyAlongExhaustion_zero_params`). -/
theorem freeEnergyAlongExhaustion_zero_params_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_zero_params G Λ β n hn

/-- **β=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis via
`Exhaustion.eventually_volume_nonempty`. -/
theorem freeEnergyInfinite_beta_zero_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_eventually_nonempty G Λ J h
    Λ.eventually_volume_nonempty

/-- **J=h=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis. -/
theorem freeEnergyInfinite_zero_params_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_eventually_nonempty G Λ β
    Λ.eventually_volume_nonempty

/-- **J=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis. -/
theorem freeEnergyInfinite_J_zero_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_eventually_nonempty G Λ h β
    Λ.eventually_volume_nonempty

/-- **Infinite-volume J=0 graph-independence**:
`freeEnergyInfinite G Λ ⟨0, h, β⟩ = freeEnergyInfinite ⊥ Λ ⟨0, h, β⟩`
for any ambient graph `G, Λ`, any `h, β`.

Lift of `freeEnergyAlongExhaustion_eq_bot_at_J_zero` (PR #176): the
stagewise graph independence propagates through `Filter.limsup` since
the two sequences are pointwise equal. -/
theorem freeEnergyInfinite_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_eq_bot_at_J_zero G Λ h β n

end Ambient

end IsingModel
