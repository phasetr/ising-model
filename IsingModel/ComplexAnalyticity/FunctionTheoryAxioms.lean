import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ClusterPt

/-!
# Isolated function-theory axioms (out of scope for the lattice-Ising library)

This module collects **pure complex-analysis (function-theory) results** that are needed elsewhere
in the project but that are **not about the Ising model** and that Mathlib does not (yet) provide.
Per
the project scope policy (`docs/index.md` § Axioms), such results are **isolated here as
clearly-labelled `axiom`s and are deliberately not proven**: proving them would amount to building a
bespoke complex-analysis library inside a lattice-model project, which is not this project's
responsibility.  The Ising-side content that *feeds* these axioms (volume-uniform cluster-expansion
bounds, real-axis convergence, …) is in scope and is proven in the usual way.

Each axiom here must be (i) pure function theory, unrelated to the Ising model; (ii) absent from
Mathlib; (iii) confined to this module; (iv) documented with its precise statement and the reason it
is out of scope.

## Axioms
* `vitaliPorter_tendstoLocallyUniformlyOn` — the **Vitali–Porter convergence theorem**.

This is the *only* non-Ising axiom in the project; everything else is `sorry`-free and proven
(modulo Mathlib).
-/

namespace IsingModel

namespace FunctionTheory

open Filter Topology

/-- **Vitali–Porter convergence theorem** (classical function theory; absent from Mathlib).

Let `U ⊆ ℂ` be open and preconnected, and `F : ℕ → ℂ → ℂ` a sequence of functions each holomorphic
on `U` (`DifferentiableOn ℂ (F n) U`).  Suppose the family is **locally uniformly bounded** on `U`:
every
`z ∈ U` has a ball `Metric.ball z r ⊆ U` (`r > 0`) and a bound `M` with `‖F n w‖ ≤ M` for all `n`
and all `w` in that ball.  Suppose moreover that `F n` converges pointwise, as `n → ∞`, on a subset
`S ⊆ U` that has an accumulation point `z₀ ∈ U` (`AccPt z₀ (𝓟 S)`), with pointwise limit `g` on `S`.

Then `F n` converges **locally uniformly** on `U` to a function `f` that is holomorphic on `U` and
agrees with the pointwise limit `g` on `S`.

This is the standard normal-families / Montel + analytic-continuation argument of one-variable
complex analysis.  It is **out of scope** for this lattice-Ising-model formalization and is
**isolated here as a deliberately-unproven axiom** (per `docs/index.md` § Axioms).  It is the bridge
that turns the (Ising-side, proven) volume-uniform bound on the finite-volume complex correlations
plus their real-axis convergence into the locally-uniform convergence needed for infinite-volume
correlation analyticity (GJ §18.6/§18.7, Issue #4230).

References: e.g. Conway, *Functions of One Complex Variable I*, VII.§2–3 (Montel's theorem and
Vitali's theorem); the Vitali–Porter theorem. -/
axiom vitaliPorter_tendstoLocallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z r, ‖F n w‖ ≤ M)
    {S : Set ℂ} (hSU : S ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hacc : AccPt z₀ (Filter.principal S))
    {g : ℂ → ℂ} (hpt : ∀ z ∈ S, Filter.Tendsto (fun n => F n z) Filter.atTop (nhds (g z))) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn F f Filter.atTop U ∧ Set.EqOn f g S

end FunctionTheory

end IsingModel
