import IsingModel.Conditioning.CorrelationClosed.GeneralFieldClosed
import IsingModel.ClusterExpansion.FieldPolymerComplexNonvanishing

/-!
# Complex-`h` general-boundary field two-point numerator (GJ §17.6.1, brick F4b-1)

Brick F4b-1 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  Brick F4a
(`GeneralFieldClosed.lean`) supplied the honest real closed form
\[
\langle\sigma_A\rangle_p
  = \frac{\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X\,\triangle\,A|}}
         {\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X|}},
\]
with `∂X = oddBoundary X` and `△ = symmDiff`.  This file complexifies **only the
field parameter** `b` (the coupling `a` stays real, matching Theorem 17.6.1's
`∂/∂h` and the existing complex prelude `fieldPolymerWeightℂ`):
\[
\mathrm{Num}^{\mathbb C}(A,a,b)
  = \sum_{X\subseteq E}(\tanh a : \mathbb C)^{|X|}\,
    (\tanh_{\mathbb C} b)^{|\partial X\,\triangle\,A|}.
\]
The field exponent `|∂X △ A|` is a `Nat`, so the complex power is `Monoid.npow`
(no `cpow` branch cut).  Because `Complex.tanh` has poles at `i(π/2 + kπ)` it is
**not entire**; the numerator is a finite sum of `Nat` powers of `Complex.tanh b`,
so the honest analyticity statement is `AnalyticOnNhd ℂ` on `Metric.ball 0 r`
with `r ≤ π/2` (the pole-free ball), mirroring `fieldPolymerZℂ_analyticOnNhd`.

Scope of F4b-1: the complex numerator definition, its real-`b`-axis agreement
`fieldTwoPointNumℂ_ofReal` (valid for all real `b`, independent of the ball), and
its local analyticity `fieldTwoPointNumℂ_analyticOnNhd`.  The complex denominator
bridge (`fieldPolymerZℂ = all-subgraphs ℂ`) and the complex-`h` correlation ratio
are deferred to F4b-2.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.6, Theorem 17.6.1, p. 313; §18.3,
  pp. 378–386 (high-temperature representation).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3,
  eqs. (3.41)–(3.46), pp. 116–117.
-/

namespace IsingModel

open Finset
open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Complex-`h` general-boundary field two-point numerator** (GJ §17.6.1, brick
F4b-1): for a finite `SimpleGraph G`, coupling `a : ℝ`, complex field `b : ℂ` and
observable `A : Finset ι`,
\[
\mathrm{Num}^{\mathbb C}(A,a,b)
  = \sum_{X\subseteq E}(\tanh a : \mathbb C)^{|X|}\,
    (\tanh_{\mathbb C} b)^{|\partial X\,\triangle\,A|},
\]
the complex mirror of the real F4a numerator
(`correlation_high_temp_expansion_general_h_closed`), with the field parameter `b`
made complex.  The index set `G.edgeFinset.powerset`, the odd boundary
`oddBoundary X` and the symmetric difference `∂X △ A` are exactly those of the
real numerator.  The field exponent `|∂X △ A|` is a `Nat` (`Monoid.npow`), so no
`cpow` branch cut arises. -/
noncomputable def fieldTwoPointNumℂ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) (b : ℂ) : ℂ :=
  ∑ X ∈ G.edgeFinset.powerset,
    (Real.tanh a : ℂ) ^ X.card * (Complex.tanh b) ^ (oddBoundary X ∆ A).card

/-- **Real-axis agreement of the complex field numerator**: for real `b`,
`fieldTwoPointNumℂ G A a (b : ℂ)` is the cast of the real F4a numerator
`∑_X tanh(a)^{|X|}·tanh(b)^{|∂X △ A|}`.  The cast distributes over the finite sum
and the `Nat` powers, and `Complex.tanh b = (Real.tanh b : ℂ)` on the real axis via
`Complex.ofReal_tanh`.  Valid for **all** real `b` (independent of the ball); it
supplies the real-`b`-axis seed values for the analytic-continuation identity of
F4b-2.  Mirrors `fieldPolymerZℂ_ofReal`. -/
theorem fieldTwoPointNumℂ_ofReal (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a b : ℝ) :
    fieldTwoPointNumℂ G A a (b : ℂ)
      = ((∑ X ∈ G.edgeFinset.powerset,
            Real.tanh a ^ X.card * Real.tanh b ^ (oddBoundary X ∆ A).card : ℝ) : ℂ) := by
  unfold fieldTwoPointNumℂ
  push_cast [Complex.ofReal_tanh]
  rfl

/-- **Local analyticity of the complex field numerator** (GJ §17.6.1, brick F4b-1):
on `Metric.ball 0 r` with `r ≤ π/2`, `b ↦ fieldTwoPointNumℂ G A a b` is
`AnalyticOnNhd ℂ`.  It is a finite sum of terms `(tanh a : ℂ)^{|X|}` (constant in
`b`) times a `Nat` power of `Complex.tanh b`, analytic on the pole-free `π/2`-ball
(`analyticOnNhd_ctanh_ball`, `AnalyticAt.pow`, `AnalyticAt.mul`), and analyticity
is closed under finite sums (`Finset.analyticAt_fun_sum`).  Unconditional (no
degree-window / Kotecký–Preiss hypothesis: a finite sum needs no Weierstrass
control).  Mirrors `fieldPolymerZℂ_analyticOnNhd`. -/
theorem fieldTwoPointNumℂ_analyticOnNhd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) {r : ℝ} (hrpi : r ≤ Real.pi / 2) :
    AnalyticOnNhd ℂ (fun b : ℂ => fieldTwoPointNumℂ G A a b) (Metric.ball 0 r) := by
  intro w hw
  have hwpi : w ∈ Metric.ball (0 : ℂ) (Real.pi / 2) := by
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    exact lt_of_lt_of_le hw hrpi
  have hctanh : AnalyticAt ℂ Complex.tanh w := analyticOnNhd_ctanh_ball w hwpi
  simp only [fieldTwoPointNumℂ]
  exact Finset.analyticAt_fun_sum _ (fun X _ =>
    analyticAt_const.mul (hctanh.pow (oddBoundary X ∆ A).card))

end IsingModel
