import IsingModel.AmbientLatticeSum.LambdaSuperadditivity

/-!
# Upper bounds on the infinite-volume free energy, and its value when the stages converge

`freeEnergyInfinite G Λ p` is the `Filter.limsup` along `atTop` of the stage sequence
`freeEnergyAlongExhaustion G Λ p`, whose value at a stage `n` is the free energy of the
subgraph of `G` induced by the finite volume `Λ.volume n`. The ambient graph
`G : SimpleGraph V` and the exhaustion `Λ : Exhaustion V` are arbitrary throughout, and
every statement here takes `[DecidableEq V]` together with the stagewise `Fintype` instance
on the edge set of that induced subgraph.

The upper bounds assume a real `c` for which every stage with nonempty volume has at most
`c` times as many induced edges as vertices, and take `[Nonempty V]`, the instance under
which an exhaustion's volumes are eventually nonempty and a stagewise bound therefore
reaches the `limsup`. Neither varies with the stage: its right-hand side is a single real
number.

At an arbitrary `p` under `Ferromagnetic p` the bound reads
`freeEnergyInfinite G Λ p ≤ log 2 + |p.β| * (|p.J| * c + |p.h|)`. At the zero field, with the
ferromagnetic hypothesis unbundled as `0 ≤ J` and `0 < β`, it reads
`freeEnergyInfinite G Λ ⟨J, 0, β⟩ ≤ log 2 + β * J * c`; under those two sign hypotheses the
first right-hand side, evaluated at `h = 0`, is that same real number.

The value equation carries none of that apparatus: no `[Nonempty V]`, no sign hypothesis and
no hypothesis on edge counts. It says that whenever the stage sequence tends to a real `L`,
the `limsup` defining `freeEnergyInfinite` is `L`.
-/

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Uniform upper bound on `freeEnergyInfinite` under bounded edge density**:
the per-stage bound `freeEnergyAlongExhaustion_le_uniform_upper_bound` lifts to `limsup`:
`freeEnergyInfinite G Λ p ≤ log 2 + |β|·(|J|·c + |h|)` for ferromagnetic `p`.

Proof outline.
1. By `Exhaustion.exhaust`, any vertex of a nonempty `V` is
   eventually in `Λ.volume n`, so `(Λ.volume n).Nonempty` holds
   eventually (atTop).
2. Apply the per-n upper bound
   `freeEnergyAlongExhaustion_le_uniform_upper_bound` under the
   eventual hypothesis — this gives the `∀ᶠ`-form of the bound.
3. For `Filter.IsCoboundedUnder (· ≤ ·)`, use the (ferromagnetic)
   lower bound `freeEnergyAlongExhaustion_ge_log_two_cosh`.
4. `Filter.limsup_le_of_le` concludes. -/
theorem freeEnergyInfinite_le_uniform_upper_bound
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ p ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  -- Eventual nonemptiness from exhaust.
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hbound : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ p n
        ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne
  have hbdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ p) := by
    refine ⟨Real.log (2 * Real.cosh (p.β * p.h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G Λ hf.hJ hf.hh hf.hβ n hne
  exact Filter.limsup_le_of_le hbdd_below.isCoboundedUnder_le hbound

/-- **∞-vol sharper `f` upper bound under bounded edge density**: under
`0 ≤ β·J`, `BoundedEdgeDensity G Λ` constant `c`, and ferromagnetic
parameters `p = ⟨J, 0, β⟩` (i.e. `0 ≤ J, 0 < β`),
`freeEnergyInfinite G Λ ⟨J, 0, β⟩ ≤ log 2 + β·J·c`.

Combines the per-stage uniform bound
`freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_uniform`
with `Filter.limsup_le_of_le`. The cobounded-under
condition is discharged via the ferromagnetic lower bound
`freeEnergyAlongExhaustion_ge_log_two_cosh` at `h = 0`.

Numerically the same bound as `freeEnergyInfinite_le_uniform_upper_bound`
at `h = 0`: that lemma's `log 2 + |β|·(|J|·c + |h|)` collapses to
`log 2 + β·J·c` under `0 ≤ J`, `0 < β`, `h = 0`. What this statement adds
is the specialized form, not a sharper constant. (`Real.cosh` occurs in
neither conclusion; it enters only through the lower bound
`freeEnergyAlongExhaustion_ge_log_two_cosh` used to discharge
coboundedness in both proofs.) -/
theorem freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * c := by
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hbound : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.log 2 + β * J * c := by
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_uniform
      G Λ J β hβJ hc n hne
  have hbdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β * 0)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := J) (h := 0) (β := β) G Λ hJ (le_refl 0) hβ n hne
  exact Filter.limsup_le_of_le hbdd_below.isCoboundedUnder_le hbound

/-- **`freeEnergyInfinite` is the limit when `freeEnergyAlongExhaustion`
converges**: if the sequence `n ↦ freeEnergyAlongExhaustion G Λ p n`
has a limit `L`, then `freeEnergyInfinite G Λ p = L`.

Follows from `freeEnergyInfinite := Filter.limsup …` and
`Filter.Tendsto.limsup_eq` (convergent sequence's `limsup` equals its
limit).

Infrastructure for the pending §4.6 Prop 4.6.1 Fekete convergence:
once convergence is established, this gives the value equation for
`freeEnergyInfinite`. -/
theorem freeEnergyInfinite_eq_of_tendsto
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds L)) :
    freeEnergyInfinite G Λ p = L := by
  unfold freeEnergyInfinite
  exact h.limsup_eq

end Ambient

end IsingModel
