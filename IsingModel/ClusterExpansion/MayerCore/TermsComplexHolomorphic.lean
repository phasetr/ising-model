import IsingModel.ClusterExpansion.MayerCore.TermsComplex
import IsingModel.ClusterExpansion.MayerTermTailSummability
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy of the complex Mayer series on a Kotecky--Preiss ball (GJ §18.6)

This is PR-B of issue #4149 (§18.6).  Building on the per-term entirety of
`mayerExpansionTermComplex` (PR-A, `MayerCore/TermsComplex.lean`), this file proves the full
complexified Mayer series

`z ↦ ∑' n, mayerExpansionTermComplex G n z`

is holomorphic (`DifferentiableOn ℂ`) on the open ball `ball 0 R`, whenever the per-site
Kotecky--Preiss tail condition holds at radius `R` (`Δ²eR < 1` and `4·Δ²eR/(1−Δ²eR)² < 1`).

The mechanism is the Weierstrass criterion
(`Complex.differentiableOn_tsum_of_summable_norm`): each term is entire (PR-A) and the term
norms are dominated, on the ball, by a summable geometric majorant.  The majorant is the
*same* geometric per-order bound `|V|/(1−r)·(4r/(1−r)²)^n` already proven for the real Mayer
terms (`mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`): the term-norm-to-tree-sum
step is re-derived directly on the complex norm (it is the triangle inequality, which mirrors
`mayerExpansionTerm_abs_le_treeSum_activity`'s per-`ω` `hpw`), and the downstream
tree-sum-to-geometric chain (`penroseTreeSum_le_sum_pow_peelBound`,
`sum_pow_rootedParentActivePeelBound_le`) is reused verbatim through the real lemma evaluated
at `t := ‖z‖`.

This is a sufficient-condition holomorphy statement for the *finite-graph* Mayer series; it is
not the sharp Kotecky--Preiss criterion, nor a statement about the thermodynamic limit.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.5--§18.6, pp.~335--340.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Norm of the complexified cluster-sequence activity**: `‖z(ω)‖ = ∏ i, ‖z‖^{|ω i|}`, the
norm distributing over the monomial product (`norm_prod`, `Complex.norm_pow`).  The product on
the right is definitionally `clusterSeqActivity ‖z‖ ω`. -/
theorem clusterSeqActivityComplex_norm (z : ℂ) {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    ‖clusterSeqActivityComplex z ω‖ = ∏ i : Fin n, ‖z‖ ^ (ω i).card := by
  rw [clusterSeqActivityComplex, norm_prod]
  exact Finset.prod_congr rfl (fun i _ => Complex.norm_pow z (ω i).card)

/-- **The complex Mayer term norm is bounded by the real term-absolute sum at `‖z‖`.**
By the triangle inequality `‖∑‖ ≤ ∑‖·‖` and the activity-norm factorisation, the norm of
`mayerExpansionTermComplex G n z` is at most the real term-absolute sum
`∑_ω |ϕ^T(ω)|·z(‖z‖,ω)` (with `z(‖z‖,ω) = clusterSeqActivity ‖z‖ ω ≥ 0`).  This is the
complex analogue of `mayerExpansionTerm_abs_le`. -/
theorem mayerExpansionTermComplex_norm_le_termAbsSum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (z : ℂ) :
    ‖mayerExpansionTermComplex G n z‖
      ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
          |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ω _ => le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, clusterSeqActivityComplex_norm,
    clusterSeqActivity]

/-- **The real term-absolute sum is bounded by the tree sum of activities.**  For each order
`n`, `∑_ω |ϕ^T(ω)|·z(t,ω) ≤ (n!)⁻¹·∑_ω ∑_{T tree of incompat(ω)} ∏_i |t|^{|ω i|}` when
`0 ≤ t` (so `z(t,ω) = |z(t,ω)|`).  This is the per-`ω` `hpw` step of
`mayerExpansionTerm_abs_le_treeSum_activity` without the leading `|mayer| ≤ ·`, isolating the
term-sum-to-tree-sum reuse for the complex norm route. -/
theorem termAbsSum_le_treeSum_activity (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ((n.factorial : ℝ)⁻¹)
        * ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              ∏ i : Fin n, |t| ^ (ω i).card := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hact : clusterSeqActivity t ω = |clusterSeqActivity t ω| := by
    rw [abs_of_nonneg (by rw [clusterSeqActivity]; positivity)]
  rw [hact, clusterSeqActivity_abs]
  calc |ursellCoefficient ω| * ∏ i : Fin n, |t| ^ (ω i).card
      ≤ ((Penrose.numSpanningTrees (polymerSeqIncompatibilityGraph ω) : ℝ)
          / n.factorial) * ∏ i : Fin n, |t| ^ (ω i).card :=
        mul_le_mul_of_nonneg_right
          (ursellCoefficient_abs_le_numSpanningTrees_div_factorial ω) (by positivity)
    _ = ((n.factorial : ℝ)⁻¹)
          * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              ∏ i : Fin n, |t| ^ (ω i).card := by
        rw [Finset.sum_const, nsmul_eq_mul, Penrose.numSpanningTrees]
        ring

/-- **The shifted real term-absolute sum is bounded by the tree-sum exp-activity form.**
Splitting off the root vertex `0` and inserting the Kotecky--Preiss weights `e^{|ω(succ i)|} ≥
1` on the non-root factors, for `0 ≤ t`,
`∑_ω |ϕ^T(ω)|·z(t,ω) ≤ ((n+1)!)⁻¹·∑_ω ∑_{T tree of incompat(ω)} |t|^{|ω 0|}·∏_i
e^{|ω(succ i)|}·|t|^{|ω(succ i)|}`.  This mirrors `mayerExpansionTerm_succ_abs_le_treeSum_-
rootedExpActivity` but enters through the term-absolute sum (not `|mayer|`). -/
theorem termAbsSum_succ_le_treeSum_rootedExpActivity (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (((n + 1).factorial : ℝ)⁻¹)
        * ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
            ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
              |t| ^ (ω 0).card *
                ∏ i : Fin n,
                  Real.exp 1 ^ (ω (Fin.succ i)).card * |t| ^ (ω (Fin.succ i)).card := by
  refine (termAbsSum_le_treeSum_activity G (n + 1) ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun ω _ => ?_
  refine Finset.sum_le_sum fun T _ => ?_
  rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  refine le_mul_of_one_le_left (by positivity) ?_
  exact one_le_pow₀ (Real.one_le_exp_iff.mpr zero_le_one)

/-- **Geometric per-order bound on the shifted real term-absolute sum.**  For `0 ≤ t` and
`Δ²e|t| < 1`,
`∑_ω |ϕ^T(ω)|·z(t,ω) ≤ |V|/(1−r)·(4r/(1−r)²)^n`  (`r = Δ²e|t|`, summed at order `n+1`).
This mirrors `mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`, entering through the
term-absolute sum: `termAbsSum_succ_le_treeSum_rootedExpActivity` then the *reused* downstream
chain `penroseTreeSum_le_sum_pow_peelBound` / `sum_pow_rootedParentActivePeelBound_le` and the
same `(n+1)!⁻¹·n! ≤ 1` arithmetic. -/
theorem termAbsSum_succ_le_card_div_mul_geometric (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  -- Term-sum → tree-sum → peel-sum, reusing the existing downstream chain.
  refine (termAbsSum_succ_le_treeSum_rootedExpActivity G n ht).trans ?_
  refine (mul_le_mul_of_nonneg_left (penroseTreeSum_le_sum_pow_peelBound G n hkp)
    (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left (sum_pow_rootedParentActivePeelBound_le G n hkp)
    (by positivity)).trans ?_
  -- ((n+1)!)⁻¹ · (rr^n·|V|·4^n·n!)/q^{2n+1} ≤ |V|/q · (4rr/q²)^n.
  have hfact : ((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2 : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by rw [pow_succ, pow_mul]
  have hgoal_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / q
      * (4 * rr / q ^ 2) ^ n := by positivity
  have hLHS : ((n + 1).factorial : ℝ)⁻¹
        * ((rr ^ n * (Fintype.card ι : ℝ) * (4 : ℝ) ^ n * (n.factorial : ℝ))
            / q ^ (2 * n + 1))
      = (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
          * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n) := by
    rw [div_pow, mul_pow, hq2]
    field_simp
    ring
  rw [hLHS]
  calc (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
        * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n)
      ≤ 1 * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_right hfact hgoal_nonneg
    _ = (Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n := one_mul _

/-- **Geometric per-order bound on the shifted complex Mayer term norm.**  For `Δ²e‖z‖ < 1`,
`‖mayerExpansionTermComplex G (n+1) z‖ ≤ |V|/(1−r)·(4r/(1−r)²)^n` with `r = Δ²e‖z‖`.  Combines
the complex term-norm/term-sum bound (`mayerExpansionTermComplex_norm_le_termAbsSum` at `z`)
with the geometric bound on the real term-absolute sum at `t := ‖z‖` (using `|‖z‖| = ‖z‖`). -/
theorem mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ) {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1) :
    ‖mayerExpansionTermComplex G (n + 1) z‖
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2) ^ n := by
  have habs : |‖z‖| = ‖z‖ := abs_of_nonneg (norm_nonneg z)
  have hkp' : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|) < 1 := by rw [habs]; exact hkp
  refine (mayerExpansionTermComplex_norm_le_termAbsSum G (n + 1) z).trans ?_
  have h := termAbsSum_succ_le_card_div_mul_geometric G n (norm_nonneg z) hkp'
  rw [habs] at h
  exact h

/-- **Monotonicity of `|V|/(1−r)·(4r/(1−r)²)^n` in `r`** on the Kotecky--Preiss region.  If
`0 ≤ r₁ ≤ r₂`, `r₂ < 1` and `4r₂/(1−r₂)² < 1`, then the geometric per-order majorant is
larger at `r₂`.  Both factors are increasing in `r`: `1/(1−r)` increases (denominator
positive, decreasing) and `(4r/(1−r)²)^n` increases (nonneg base increasing, via
`ratio_mono`-style cross-multiplication and `pow_le_pow_left₀`). -/
theorem geometricMajorant_mono_of_le {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂)
    (hr2 : r₂ < 1) (V n : ℕ) :
    (V : ℝ) / (1 - r₁) * (4 * r₁ / (1 - r₁) ^ 2) ^ n
      ≤ (V : ℝ) / (1 - r₂) * (4 * r₂ / (1 - r₂) ^ 2) ^ n := by
  have hr1 : r₁ < 1 := lt_of_le_of_lt h12 hr2
  have hq1 : (0 : ℝ) < 1 - r₁ := by linarith
  have hq2 : (0 : ℝ) < 1 - r₂ := by linarith
  -- `1/(1−r)` increasing: smaller positive denominator at `r₂`.
  have hcardmono : (V : ℝ) / (1 - r₁) ≤ (V : ℝ) / (1 - r₂) :=
    div_le_div_of_nonneg_left (by positivity) hq2 (by linarith)
  -- `4r/(1−r)²` increasing.
  have hρmono : 4 * r₁ / (1 - r₁) ^ 2 ≤ 4 * r₂ / (1 - r₂) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (r₂ - r₁), mul_nonneg h0 (le_of_lt hq2), mul_pos hq1 hq2]
  have hρ1nonneg : (0 : ℝ) ≤ 4 * r₁ / (1 - r₁) ^ 2 := by positivity
  calc (V : ℝ) / (1 - r₁) * (4 * r₁ / (1 - r₁) ^ 2) ^ n
      ≤ (V : ℝ) / (1 - r₂) * (4 * r₁ / (1 - r₁) ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right hcardmono (by positivity)
    _ ≤ (V : ℝ) / (1 - r₂) * (4 * r₂ / (1 - r₂) ^ 2) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ1nonneg hρmono n)
          (by positivity)

/-- **Holomorphy of the complex Mayer series on a Kotecky--Preiss ball (GJ §18.6).**  If
`0 ≤ R` and the per-site Kotecky--Preiss tail condition holds at radius `R` — `Δ²eR < 1` and
`4·Δ²eR/(1−Δ²eR)² < 1` — then `z ↦ ∑' n, mayerExpansionTermComplex G n z` is
`DifferentiableOn ℂ` on `ball 0 R`.

Weierstrass (`Complex.differentiableOn_tsum_of_summable_norm`): each term is entire
(`mayerExpansionTermComplex_differentiableOn`, PR-A) and the term norms on the ball are
dominated by a summable majorant `u`.  `u 0` bounds the constant `n = 0` term (its norm at
`z = 0`, a fixed value); `u (k+1)` is the geometric majorant at `r = Δ²eR`, summable since
its ratio is `< 1` and dominating `‖mayerExpansionTermComplex G (k+1) z‖` on the ball via the
geometric per-order bound at `‖z‖` and monotonicity in `r` (`geometricMajorant_mono_of_le`,
using `‖z‖ ≤ R`). -/
theorem mayerExpansionTermComplex_tsum_differentiableOn_ball (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {R : ℝ} (hR : 0 ≤ R)
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, mayerExpansionTermComplex G n z)
      (Metric.ball (0 : ℂ) R) := by
  set rR : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) with hrR
  set qR : ℝ := 1 - rR with hqR
  have hqRpos : 0 < qR := by rw [hqR]; linarith [hkpR]
  have hrR0 : 0 ≤ rR := by rw [hrR]; positivity
  set ρR : ℝ := 4 * rR / qR ^ 2 with hρRdef
  have hρR0 : 0 ≤ ρR := by rw [hρRdef]; positivity
  -- The geometric majorant `(card/(1−rR))·ρR^k` is summable.
  have hgeo : Summable fun k : ℕ => (Fintype.card ι : ℝ) / qR * ρR ^ k :=
    (summable_geometric_of_lt_one hρR0 hρR).mul_left _
  -- The majorant family: head bound at `k = 0`, geometric majorant for `k+1`.
  set u : ℕ → ℝ := fun k => Nat.rec
    (‖mayerExpansionTermComplex G 0 (0 : ℂ)‖)
    (fun k _ => (Fintype.card ι : ℝ) / qR * ρR ^ k) k with hu
  have hu0 : u 0 = ‖mayerExpansionTermComplex G 0 (0 : ℂ)‖ := rfl
  have husucc : ∀ k, u (k + 1) = (Fintype.card ι : ℝ) / qR * ρR ^ k := fun _ => rfl
  -- `u` is summable: tail (shift by 1) is the geometric majorant.
  have huSummable : Summable u := by
    rw [← summable_nat_add_iff 1]
    refine hgeo.congr fun k => ?_
    rw [husucc k]
  -- Term norms are bounded by `u` on the ball.
  have hbound : ∀ k : ℕ, ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) R →
      ‖mayerExpansionTermComplex G k w‖ ≤ u k := by
    intro k w hw
    have hwnorm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hwle : ‖w‖ ≤ R := le_of_lt hwnorm
    cases k with
    | zero =>
        -- `mayerExpansionTermComplex G 0 ·` is constant: equal at `w` and `0`.
        rw [hu0]
        have hconst : mayerExpansionTermComplex G 0 w = mayerExpansionTermComplex G 0 (0 : ℂ) := by
          unfold mayerExpansionTermComplex clusterSeqActivityComplex
          simp
        rw [hconst]
    | succ k =>
        rw [husucc k]
        -- `‖z‖ ≤ R` ⟹ KP holds at `‖z‖`; geometric bound at `‖z‖` ≤ majorant at `R`.
        have hrwle : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖w‖) ≤ rR := by
          rw [hrR]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hwle (le_of_lt (Real.exp_pos 1))
        have hkpw : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖w‖) < 1 :=
          lt_of_le_of_lt hrwle hkpR
        refine (mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric G k hkpw).trans ?_
        have h0w : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖w‖) := by positivity
        exact geometricMajorant_mono_of_le h0w hrwle hkpR (Fintype.card ι) k
  exact Complex.differentiableOn_tsum_of_summable_norm huSummable
    (fun k => mayerExpansionTermComplex_differentiableOn G k _) Metric.isOpen_ball hbound

end IsingModel
