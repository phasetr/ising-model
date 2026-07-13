import IsingModel.ClusterExpansion.FieldAvoidingRatio

/-!
# Volume-uniform complex field polymer non-vanishing (GJ §17.6.1, brick F6b)

Discharges the volume-uniform partition non-vanishing hypothesis `hden` consumed by the
infinite-volume field-correlation analyticity capstone
(`fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound`, brick F6a,
`FieldCorrelationVitali.lean`), for the lattice exhaustion, in the `∂/∂h` (field) setting of
GJ §17.6.1 (Issue #4433).

The argument is a purely mechanical two-variable downcast of the fixed-graph field partition
non-vanishing `fieldPolymerZℂ_ne_zero_of_degree_window` (brick F2,
`FieldExpIdentityDegreeWindow.lean`), which is phrased at the concrete `G.maxDegree` and the
field-dependent envelope
`max 1 ‖Complex.tanh b‖`.  To make it volume-uniform along the lattice exhaustion, the two
Kotecký–Preiss window hypotheses are rephrased with:

* an **external** degree bound `Δ` with `hΔ : G.maxDegree ≤ Δ` (each induced stage satisfies
  only `maxDegree ≤ 2d`, `induced_latticeGraph_maxDegree_le`, not equality), and
* a **ball-uniform** envelope `Mr` with `‖Complex.tanh b‖ ≤ Mr` on `Metric.ball 0 r`,

so that the window `Δ² · e · ((max 1 Mr)² · ρ)` becomes independent of the exhaustion stage
`n` and of the field `b`.  The `c = 2` connected-gas window `8 X/(1−X)² < 1` is closed downward
by `kpRegion8_downward_closed`; the pure non-vanishing needs **no** `Nonempty ι` hypothesis
(unlike the correlation bound `hbdd` of F5b), so it also holds on empty early exhaustion stages.

## Main results
* `fieldPolymerZℂ_ne_zero_of_degree_le` — degree-and-ball-uniform non-vanishing downcast (F6b-1);
* `fieldPolymerZℂAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph` — the `Δ = 2d` exhaustion
  wrap supplying the F6a `hden` datum (F6b-2).

The window conditions stay hyp-gated at `Δ = 2d` (their high-temperature discharge, together
with `hbdd`, is brick F6c).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §17.6.1.
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Degree-and-ball-uniform field partition non-vanishing** (GJ §17.6.1, brick F6b-1).  A
degree-uniform, ball-uniform generalization of `fieldPolymerZℂ_ne_zero_of_degree_window`
(F2): both Kotecký–Preiss window hypotheses are phrased with an **external** degree bound `Δ`
(`hΔ : G.maxDegree ≤ Δ`) and a **ball-uniform** field envelope `Mr` (`‖Complex.tanh b‖ ≤ Mr`
on `Metric.ball 0 r`) instead of the concrete `G.maxDegree` and the field-dependent
`max 1 ‖Complex.tanh b‖`.  This makes the non-vanishing conclusion `fieldPolymerZℂ G a b ≠ 0`
uniform across an exhaustion of induced graphs (each satisfying only `maxDegree ≤ 2d`) and
across the ball.

No new content beyond F2: the window at the concrete `(G.maxDegree, ‖Complex.tanh b‖)` is
recovered from the `(Δ, Mr)`-window by the two monotonicities `(G.maxDegree:ℝ)² ≤ (Δ:ℝ)²`
(`pow_le_pow_left₀`) and `max 1 ‖Complex.tanh b‖ ≤ max 1 Mr` (`max_le_max`), closed downward
by `kpRegion8_downward_closed` (the `c = 2` connected gas).  The non-vanishing needs no
`Nonempty ι` hypothesis.  The non-vanishing mirror of the norm bound
`fieldCorrelationℂ_norm_le_ball_uniform_of_degree_le` (F5b-2). -/
theorem fieldPolymerZℂ_ne_zero_of_degree_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (Δ : ℕ) (hΔ : G.maxDegree ≤ Δ)
    {a Awin r Mr ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkpstar : (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)) < 1)
    (hρwinstar : 8 * ((Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)))
        / (1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ))) ^ 2 < 1) :
    fieldPolymerZℂ G a b ≠ 0 := by
  -- `‖tanh b‖ ≤ Mr` on the ball, hence `max 1 ‖tanh b‖ ≤ max 1 Mr`.
  have hbnorm : ‖b‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hbr)
  have htb : ‖Complex.tanh b‖ ≤ Mr := hMr b hbnorm
  have hcast : (G.maxDegree : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  -- the concrete window argument `X_G` and the external `X_Δ`; `0 ≤ X_G ≤ X_Δ`.
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) := by positivity
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))
      ≤ (Δ : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)) := by gcongr
  -- downcast the `c = 2` connected-gas window `Δ → G.maxDegree`, `Mr → ‖tanh b‖`.
  obtain ⟨hkp_G, hρwin_G⟩ := kpRegion8_downward_closed h0 h12 hkpstar hρwinstar
  exact fieldPolymerZℂ_ne_zero_of_degree_window G ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp_G hρwin_G

namespace Ambient

/-- **Volume-uniform field partition non-vanishing along the lattice exhaustion**
(GJ §17.6.1, brick F6b-2).  For the lattice exhaustion, a single ball radius `r` and a single
set of `Δ = 2d` window hypotheses supply `fieldPolymerZℂ (inducedGraph (latticeGraph d)
(Λ.volume n)) a b ≠ 0` for **every** exhaustion stage `n` and every field `b ∈ Metric.ball 0 r`
— exactly the `hden` datum consumed by the F6a capstone
`fieldCorrelationℂAlongExhaustion_analytic_of_volume_uniform_bound`.

Proof: each induced stage has `maxDegree ≤ 2d` (`induced_latticeGraph_maxDegree_le`), so the
degree-and-ball-uniform downcast `fieldPolymerZℂ_ne_zero_of_degree_le` at `Δ = 2d` applies
stage-by-stage on a single `n`-independent window.  No `Nonempty` hypothesis is required, so
the bound also holds on empty early stages.  The field mirror of the `β`-route
`partitionFunctionComplexAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph`.  The window
stays hyp-gated at `Δ = 2d`; its high-temperature discharge is brick F6c. -/
theorem fieldPolymerZℂAlongExhaustion_ne_zero_on_ball_uniform_latticeGraph
    (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (latticeGraph d) (Λ.volume n)).edgeSet]
    {a Awin r Mr ρ : ℝ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkpstar : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)) < 1)
    (hρwinstar : 8 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ)))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ((max 1 Mr) ^ 2 * ρ))) ^ 2 < 1) :
    ∀ n : ℕ, ∀ b ∈ Metric.ball (0 : ℂ) r,
      fieldPolymerZℂ (inducedGraph (latticeGraph d) (Λ.volume n)) a b ≠ 0 := by
  classical
  intro n b hb
  exact fieldPolymerZℂ_ne_zero_of_degree_le
    (inducedGraph (latticeGraph d) (Λ.volume n)) (2 * d)
    (induced_latticeGraph_maxDegree_le d (Λ.volume n))
    ha hr0 hrpi hMr1 hMr hb hρ0 htanhA hkpstar hρwinstar

end Ambient

end IsingModel
