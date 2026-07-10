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

/-! ## F4b-2a: complex all-subgraphs ↔ families denominator bridge

The complex denominator of the field two-point ratio is the `A = ∅`
specialization `fieldTwoPointNumℂ G ∅ a b` (since `∂X △ ∅ = ∂X`).  To transport
the non-vanishing `fieldPolymerZℂ_ne_zero` (F2, Kotecký–Preiss window) to the
denominator we bridge it to the complex field polymer partition function
`fieldPolymerZℂ`.  This is the verbatim complex mirror of the real bridge
`allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`
(`Families/FieldConnectedPolymers.lean`): the bijection `X ↔ polymerDecomposition X`
is weight-independent (reused named lemmas), only the terminal ring identity moves
from `ℝ` to `ℂ`.  A `push_cast` of the real bridge would only hold on the real
`b`-axis, whereas the ratio analyticity on the `π/2`-ball needs the identity at
every complex `b`; hence the `Finset.sum_bij` is re-run over `ℂ`. -/

/-- **Complex field-weight factorization over a vertex-disjoint family**: for a
pairwise vertex-disjoint family `Γ` with `X = Γ.biUnion id`,
`fieldPolymerWeightℂ a b (Γ.biUnion id) = ∏_{P ∈ Γ} fieldPolymerWeightℂ a b P`.
The complex mirror of `fieldPolymerWeight_biUnion_of_vd`: the `tanh(a)^|·|` factor
uses cardinality additivity (`Finset.card_biUnion` via edge-disjointness), the
`(Complex.tanh b)^{#odd(·)}` factor uses `oddCard_biUnion_of_vd`; both combinatorial
inputs are ring-independent, and `Finset.prod_pow_eq_pow_sum`/`Finset.prod_mul_distrib`
hold in `ℂ`. -/
theorem fieldPolymerWeightℂ_biUnion_of_vd
    {Γ : Finset (Finset (Sym2 ι))}
    (hpair : (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    (a : ℝ) (b : ℂ) :
    fieldPolymerWeightℂ a b (Γ.biUnion id)
      = ∏ P ∈ Γ, fieldPolymerWeightℂ a b P := by
  classical
  have hcard : (Γ.biUnion id).card = ∑ P ∈ Γ, P.card := by
    apply Finset.card_biUnion
    intro P hP Q hQ hPQ
    exact (hpair (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hPQ).toEdgeDisjoint
  unfold fieldPolymerWeightℂ oddBoundary
  rw [hcard, oddCard_biUnion_of_vd hpair, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

/-- **Complex all-subgraphs ↔ families bridge** (GJ §17.6.1, brick F4b-2a): for all
`a : ℝ` and `b : ℂ`,
`fieldPolymerZℂ G a b =
  ∑_{X ⊆ E} (tanh a : ℂ)^{|X|}·(Complex.tanh b)^{|∂X|}`,
the complex mirror of `allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`.  Proved
by re-running the same `Finset.sum_bij` along `X ↔ polymerDecomposition X` between
`G.edgeFinset.powerset` and `vdConnectedPolymerFamilies G`; the membership,
injectivity and surjectivity obligations are weight-free and reuse the real named
lemmas (`polymerDecomposition_pairwise_vertexDisjoint`,
`polymerDecomposition_biUnion_id`, `polymerDecomposition_biUnion_of_pairwiseVertexDisjoint`),
while the weight match is supplied by `fieldPolymerWeightℂ_biUnion_of_vd`.  The
right-hand side is written in `oddBoundary` form so that, after simplifying
`∂X △ ∅ = ∂X`, it matches `fieldTwoPointNumℂ G ∅` (see the capstone
`fieldTwoPointNumℂ_empty_eq_fieldPolymerZℂ`).

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117 (2017 ed.) (`h = 0`
template); Glimm–Jaffe §18.4 (lattice cluster expansion, field version). -/
theorem fieldPolymerZℂ_eq_allSubgraphs_sumℂ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a : ℝ) (b : ℂ) :
    fieldPolymerZℂ G a b
      = ∑ X ∈ G.edgeFinset.powerset,
          (Real.tanh a : ℂ) ^ X.card * (Complex.tanh b) ^ (oddBoundary X).card := by
  classical
  unfold fieldPolymerZℂ
  refine Eq.symm ?_
  apply Finset.sum_bij
    (fun X (_ : X ∈ G.edgeFinset.powerset) => polymerDecomposition X)
  · -- Membership: polymerDecomposition X ∈ vdConnectedPolymerFamilies G.
    intro X hX
    rw [Finset.mem_powerset] at hX
    rw [mem_vdConnectedPolymerFamilies]
    refine ⟨?_, polymerDecomposition_pairwise_vertexDisjoint⟩
    intro C hC
    rw [mem_allConnectedPolymers]
    rw [mem_polymerDecomposition] at hC
    obtain ⟨e, he, rfl⟩ := hC
    exact edgeComponent_isConnectedPolymer hX he
  · -- Injectivity via polymerDecomposition_biUnion_id.
    intro X _ X' _ h_eq
    have h₁ : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have h₂ : (polymerDecomposition X').biUnion id = X' :=
      polymerDecomposition_biUnion_id X'
    rw [← h₁, ← h₂, h_eq]
  · -- Surjectivity: given Γ, take X = Γ.biUnion id.
    intro Γ hΓ
    rw [mem_vdConnectedPolymerFamilies] at hΓ
    obtain ⟨hsub, hpair⟩ := hΓ
    have hconn : ∀ P ∈ Γ, IsEdgeConnected P := fun P hP =>
      (mem_allConnectedPolymers.mp (hsub hP)).connected
    have hne : ∀ P ∈ Γ, P.Nonempty := fun P hP =>
      (mem_allConnectedPolymers.mp (hsub hP)).nonempty
    refine ⟨Γ.biUnion id, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨P, hP, heP⟩ := he
      exact (mem_allConnectedPolymers.mp (hsub hP)).subset heP
    · exact polymerDecomposition_biUnion_of_pairwiseVertexDisjoint hpair hconn
        hne
  · -- Weight match via fieldPolymerWeightℂ_biUnion_of_vd.
    intro X _
    have h_biU : (polymerDecomposition X).biUnion id = X :=
      polymerDecomposition_biUnion_id X
    have hw := fieldPolymerWeightℂ_biUnion_of_vd
      (polymerDecomposition_pairwise_vertexDisjoint (X := X)) a b
    rw [h_biU] at hw
    exact hw

/-- **Complex field denominator ↔ polymer partition function** (GJ §17.6.1, brick
F4b-2a capstone): the empty-observable complex numerator is the complex field
polymer partition function,
`fieldTwoPointNumℂ G ∅ a b = fieldPolymerZℂ G a b`.  Since `by simp` reduces
`∂X △ ∅` to `∂X`, the `A = ∅` numerator is the all-subgraphs sum, identified with
`fieldPolymerZℂ` by `fieldPolymerZℂ_eq_allSubgraphs_sumℂ`.  This is the denominator
bridge for the complex-`h` correlation ratio (F4b-2b): it transports the F2
non-vanishing `fieldPolymerZℂ_ne_zero` (Kotecký–Preiss window) to the denominator,
enabling `AnalyticAt.div` on the pole-free `π/2`-ball.  The complex correlation
ratio object itself is deferred to F4b-2b. -/
theorem fieldTwoPointNumℂ_empty_eq_fieldPolymerZℂ (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a : ℝ) (b : ℂ) :
    fieldTwoPointNumℂ G ∅ a b = fieldPolymerZℂ G a b := by
  unfold fieldTwoPointNumℂ
  have hsd : ∀ X : Finset (Sym2 ι),
      oddBoundary X ∆ (∅ : Finset ι) = oddBoundary X := fun X => by simp
  simp only [hsd]
  rw [← fieldPolymerZℂ_eq_allSubgraphs_sumℂ]

end IsingModel
