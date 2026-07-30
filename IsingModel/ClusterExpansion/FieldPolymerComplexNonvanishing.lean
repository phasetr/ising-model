import IsingModel.ClusterExpansion.FieldPolymerExpNonvanishing
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Complex field partition non-vanishing via analytic continuation in `h`
(GJ §17.6.1, brick 6)

Brick 6 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1 (`∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).  Brick 5 (`FieldPolymerExpNonvanishing.lean`)
supplied the real-`h` `exp` identity
`fieldPolymerZ = Real.exp (∑' n, fieldMayerExpansionTerm)`, the real non-vanishing,
and the *complex prelude*: the complex field weight
`fieldPolymerWeightℂ a b P = (tanh a : ℂ)^|P| · (Complex.tanh b)^{#odd(P)}`, the
complex partition `fieldPolymerZℂ`, the real-axis agreement `fieldPolymerZℂ_ofReal`,
and the `M²`-inflated majorant (`M = max(1, ‖Complex.tanh b‖)`).

This file is the **complex-analytic body**: the complex Mayer term
`fieldMayerExpansionTermℂ`, its dominated summability, the complex `exp` identity
`fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)` on a
`b`-ball, established by *analytic continuation in `b`* (identity theorem seeded on
the real axis), and the automatic complex non-vanishing
`fieldPolymerZℂ G a b ≠ 0` via `Complex.exp_ne_zero`.

The continuation shape is the `h = 0` template
`vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex`
(`MayerCore/ComplexMayerMontroll.lean`); the genuinely new inputs are the
pole-avoidance `‖b‖ < π/2 ⟹ Complex.cosh b ≠ 0` (so `Complex.tanh` is analytic on
the ball) and the `b`-uniform inflated majorant at activity `Mr²·|tanh a|` on the
closed ball, fed to `Complex.differentiableOn_tsum_of_summable_norm`.  Honest
scope: brick 6 delivers only the complex `exp` identity and `≠ 0`; the two-point
Montel local bounds are brick 7, while brick 8/F6c is the small-coupling
holomorphic local-limit endpoint with equality at one field value `b₀`.  It does
not export a real infinite-volume `HasDerivAt`; that broader contract remains
unresolved under #4790.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.6, pp. 378–386 (lattice
  cluster expansion, non-vanishing of the polymer partition function on the
  Kotecký–Preiss domain, with analytic continuation in the fugacity/field).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3 and
  §3.7.3, eqs. (3.48)–(3.49) (magnetic-field expansion).
-/

namespace IsingModel

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The complex field Mayer term and its inflated norm bound -/

/-- **Complex field cluster-sequence activity** `∏ᵢ w^ℂ_{a,b}(ω i)`.  For a cluster
sequence `ω : Fin n → Finset (Sym2 ι)` the complex activity factor is the
multiplicative product of the complex field polymer weights `fieldPolymerWeightℂ a b`
(brick 5), the complex mirror of `fieldClusterSeqActivity` with the real weight
`w_{a,b}` replaced by `w^ℂ_{a,b}` (the coupling `a` stays real, the field `b ∈ ℂ`). -/
noncomputable def fieldClusterSeqActivityℂ (a : ℝ) (b : ℂ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) : ℂ :=
  ∏ i : Fin n, fieldPolymerWeightℂ a b (ω i)

/-- **Complex field Mayer expansion `n`-th term** `∑_ω (ϕ^T(ω) : ℂ)·∏ᵢ w^ℂ_{a,b}(ω i)`.
The weight-agnostic Ursell coefficient `ursellCoefficient` is reused *verbatim* and
cast to `ℂ`; the reference universe is the connected species `allConnectedPolymers G`,
and the activity factor is `fieldClusterSeqActivityℂ`.  Complex mirror of the real
`fieldMayerExpansionTerm` (`FieldMayerTerm.lean`); the `1/n!` is already absorbed
into `ursellCoefficient`. -/
noncomputable def fieldMayerExpansionTermℂ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a : ℝ) (b : ℂ) : ℂ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
    (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω

/-- **Real-axis agreement of the complex field activity**: for real `b`,
`fieldClusterSeqActivityℂ a (b : ℂ) ω = (fieldClusterSeqActivity a b ω : ℂ)`.  The
cast distributes over the product (`Complex.ofReal_prod`) and each factor agrees by
brick 5's `fieldPolymerWeightℂ_ofReal`. -/
theorem fieldClusterSeqActivityℂ_ofReal (a b : ℝ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) :
    fieldClusterSeqActivityℂ a (b : ℂ) ω = (fieldClusterSeqActivity a b ω : ℂ) := by
  unfold fieldClusterSeqActivityℂ fieldClusterSeqActivity
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun i _ => fieldPolymerWeightℂ_ofReal a b (ω i))

/-- **Real-axis agreement of the complex field Mayer term**: for real `b`,
`fieldMayerExpansionTermℂ G n a (b : ℂ) = (fieldMayerExpansionTerm G n a b : ℂ)`.  The
cast distributes over the sum and multiplication (`Complex.ofReal_sum`,
`Complex.ofReal_mul`, `fieldClusterSeqActivityℂ_ofReal`).  Complex mirror of
`mayerExpansionTermComplex_ofReal`; feeds the real-axis seed of the continuation. -/
theorem fieldMayerExpansionTermℂ_ofReal (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a b : ℝ) :
    fieldMayerExpansionTermℂ G n a (b : ℂ) = (fieldMayerExpansionTerm G n a b : ℂ) := by
  unfold fieldMayerExpansionTermℂ fieldMayerExpansionTerm
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Complex.ofReal_mul, fieldClusterSeqActivityℂ_ofReal]

/-- **`M²`-inflated norm bound of the complex field activity**: with
`M = max(1, ‖Complex.tanh b‖)`,
`‖fieldClusterSeqActivityℂ a b ω‖ ≤ clusterSeqActivity (M²·|tanh a|) ω`.  The norm
distributes over the product (`norm_prod_le`) and factorwise
`‖w^ℂ_{a,b}(ω i)‖ ≤ (M²·|tanh a|)^{|ω i|}` (brick 5's `norm_fieldPolymerWeightℂ_le`);
`Finset.prod_le_prod` closes it (each factor non-negative).  Complex mirror of
`abs_fieldClusterSeqActivity_le`, with the inflated activity `M²·|tanh a|`. -/
theorem norm_fieldClusterSeqActivityℂ_le (a : ℝ) (b : ℂ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) :
    ‖fieldClusterSeqActivityℂ a b ω‖
      ≤ clusterSeqActivity ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ω := by
  rw [fieldClusterSeqActivityℂ, clusterSeqActivity]
  calc ‖∏ i, fieldPolymerWeightℂ a b (ω i)‖
      ≤ ∏ i, ‖fieldPolymerWeightℂ a b (ω i)‖ := norm_prod_le _ _
    _ ≤ ∏ i, ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ (ω i).card :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_fieldPolymerWeightℂ_le a b (ω i))

/-- **Complex field Mayer-term spanning-tree bound at the inflated activity**: with
`M = max(1, ‖Complex.tanh b‖)`,
`‖fieldMayerExpansionTermℂ G n a b‖ ≤ numSpanningTrees (⊤ Fin n) / n! ·
(∑_{P ∈ allConnectedPolymers G} (M²·|tanh a|)^{|P|})^n`.  Combines the triangle
inequality (`norm_sum_le`, `‖(ursell : ℂ)‖ = |ursell|`), the uniform Ursell bound
`ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial`, the activity bound
`norm_fieldClusterSeqActivityℂ_le`, and the factorised total activity
`sum_clusterSeqActivity_piFinset_connected` at `t = M²·|tanh a|`.  Complex mirror of
`fieldMayerExpansionTerm_abs_le_tree_activity_pow`. -/
theorem norm_fieldMayerExpansionTermℂ_le_tree_activity_pow (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (a : ℝ) (b : ℂ) :
    ‖fieldMayerExpansionTermℂ G n a b‖ ≤
      ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ))
        * (∑ P ∈ allConnectedPolymers G,
            ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ P.card) ^ n := by
  set C : ℝ := (Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) /
    (n.factorial : ℝ) with hC
  set t : ℝ := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have htri : ‖fieldMayerExpansionTermℂ G n a b‖ ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖ := by
    unfold fieldMayerExpansionTermℂ
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun ω _ => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine htri.trans ?_
  have hsum_le :
      (∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
          |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖)
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
            C * clusterSeqActivity t ω := by
    refine Finset.sum_le_sum (fun ω _ => ?_)
    have hcsa : 0 ≤ clusterSeqActivity t ω := by
      rw [clusterSeqActivity]
      exact Finset.prod_nonneg (fun i _ => pow_nonneg htnn _)
    calc |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖
        ≤ |ursellCoefficient ω| * clusterSeqActivity t ω :=
          mul_le_mul_of_nonneg_left (norm_fieldClusterSeqActivityℂ_le a b ω) (abs_nonneg _)
      _ ≤ C * clusterSeqActivity t ω :=
          mul_le_mul_of_nonneg_right
            (by simpa [hC] using
              ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial (ω := ω)) hcsa
  refine hsum_le.trans_eq ?_
  rw [← Finset.mul_sum, sum_clusterSeqActivity_piFinset_connected]

/-! ## Pole avoidance and analyticity of `Complex.tanh` on the `π/2`-ball -/

/-- **Pole avoidance for `Complex.cosh`**: `‖b‖ < π/2 ⟹ Complex.cosh b ≠ 0`.  Since
`Complex.cosh b = Complex.cos (b·I)` (`Complex.cos_mul_I`) and the zeros of
`Complex.cos` are `(2k+1)·π/2` (`Complex.cos_eq_zero_iff`), a zero would force
`‖b‖ = ‖b·I‖ = |2k+1|·π/2 ≥ π/2`, contradicting `‖b‖ < π/2`.  A genuinely new small
lemma: mathlib has no `Complex.cosh`-zero characterisation. -/
theorem cosh_ne_zero_of_norm_lt_pi_div_two (b : ℂ) (h : ‖b‖ < Real.pi / 2) :
    Complex.cosh b ≠ 0 := by
  intro hzero
  rw [← Complex.cos_mul_I] at hzero
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hzero
  have hbI : ‖b‖ = ‖b * Complex.I‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hodd : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
    have hne : (2 * k + 1 : ℤ) ≠ 0 := by omega
    have h1 : (1 : ℤ) ≤ |2 * k + 1| := Int.one_le_abs hne
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|2 * k + 1| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs] at h2
    push_cast at h2
    exact h2
  have hge : Real.pi / 2 ≤ ‖b‖ := by
    rw [hbI, hk,
      show (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2
          = (((2 * (k : ℝ) + 1) * Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hle : Real.pi ≤ |2 * (k : ℝ) + 1| * Real.pi :=
      le_mul_of_one_le_left Real.pi_pos.le hodd
    linarith
  exact absurd h (not_lt.mpr hge)

/-- **`Complex.tanh` is differentiable on the `π/2`-ball**:
`DifferentiableOn ℂ Complex.tanh (Metric.ball 0 (π/2))`.  As `Complex.tanh =
Complex.sinh / Complex.cosh` with `sinh`, `cosh` entire (`Complex.differentiable_sinh`,
`Complex.differentiable_cosh`) and `cosh ≠ 0` on the ball
(`cosh_ne_zero_of_norm_lt_pi_div_two`), `DifferentiableAt.div` applies pointwise. -/
theorem differentiableOn_ctanh_ball :
    DifferentiableOn ℂ Complex.tanh (Metric.ball (0 : ℂ) (Real.pi / 2)) := by
  intro w hw
  have hnorm : ‖w‖ < Real.pi / 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
  have hcosh := cosh_ne_zero_of_norm_lt_pi_div_two w hnorm
  have hd : DifferentiableAt ℂ (fun z : ℂ => Complex.sinh z / Complex.cosh z) w :=
    (Complex.differentiable_sinh w).div (Complex.differentiable_cosh w) hcosh
  exact hd.differentiableWithinAt

/-- **`Complex.tanh` is analytic on the `π/2`-ball**:
`AnalyticOnNhd ℂ Complex.tanh (Metric.ball 0 (π/2))`.  A differentiable function on
an open set is analytic (`DifferentiableOn.analyticOnNhd`, `Metric.isOpen_ball`). -/
theorem analyticOnNhd_ctanh_ball :
    AnalyticOnNhd ℂ Complex.tanh (Metric.ball (0 : ℂ) (Real.pi / 2)) :=
  differentiableOn_ctanh_ball.analyticOnNhd Metric.isOpen_ball

/-- **The complex field weight is analytic in `b` on the `π/2`-ball**: for
`w ∈ Metric.ball 0 (π/2)`, `b ↦ fieldPolymerWeightℂ a b P` is `AnalyticAt ℂ` at `w`.
It is a constant `(tanh a : ℂ)^|P|` times a power of `Complex.tanh b`, analytic on the
ball (`analyticOnNhd_ctanh_ball`, `AnalyticAt.pow`, `AnalyticAt.mul`). -/
theorem fieldPolymerWeightℂ_analyticAt (a : ℝ) (P : Finset (Sym2 ι)) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) (Real.pi / 2)) :
    AnalyticAt ℂ (fun b : ℂ => fieldPolymerWeightℂ a b P) w := by
  have hctanh : AnalyticAt ℂ Complex.tanh w := analyticOnNhd_ctanh_ball w hw
  simp only [fieldPolymerWeightℂ]
  exact analyticAt_const.mul (hctanh.pow (oddBoundary P).card)

/-! ## Holomorphy of both sides in `b` -/

/-- **LHS holomorphy**: on `Metric.ball 0 r` with `r ≤ π/2`, `b ↦ fieldPolymerZℂ G a b`
is `AnalyticOnNhd ℂ`.  It is the finite family sum of finite polymer products of the
analytic complex weights (`fieldPolymerWeightℂ_analyticAt`); analyticity is closed under
finite `sum`/`prod` (`Finset.analyticAt_fun_sum`/`_prod`).  Mirrors the `h = 0` LHS
analyticity of `vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex`. -/
theorem fieldPolymerZℂ_analyticOnNhd (G : SimpleGraph ι) [Fintype G.edgeSet] (a : ℝ)
    {r : ℝ} (hrpi : r ≤ Real.pi / 2) :
    AnalyticOnNhd ℂ (fun b : ℂ => fieldPolymerZℂ G a b) (Metric.ball 0 r) := by
  intro w hw
  have hwpi : w ∈ Metric.ball (0 : ℂ) (Real.pi / 2) := by
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    exact lt_of_lt_of_le hw hrpi
  simp only [fieldPolymerZℂ]
  exact Finset.analyticAt_fun_sum _ (fun Γ _ =>
    Finset.analyticAt_fun_prod _ (fun P _ => fieldPolymerWeightℂ_analyticAt a P hwpi))

/-- **Per-term holomorphy of the complex field Mayer term**: on `Metric.ball 0 r` with
`r ≤ π/2`, `b ↦ fieldMayerExpansionTermℂ G n a b` is `AnalyticOnNhd ℂ`.  Each term is a
finite sum of constants times finite products of the analytic complex weights
(`fieldPolymerWeightℂ_analyticAt`). -/
theorem fieldMayerExpansionTermℂ_analyticOnNhd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a : ℝ) {r : ℝ} (hrpi : r ≤ Real.pi / 2) :
    AnalyticOnNhd ℂ (fun b : ℂ => fieldMayerExpansionTermℂ G n a b) (Metric.ball 0 r) := by
  intro w hw
  have hwpi : w ∈ Metric.ball (0 : ℂ) (Real.pi / 2) := by
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    exact lt_of_lt_of_le hw hrpi
  simp only [fieldMayerExpansionTermℂ, fieldClusterSeqActivityℂ]
  refine Finset.analyticAt_fun_sum _ (fun ω _ => analyticAt_const.mul ?_)
  exact Finset.analyticAt_fun_prod _ (fun i _ => fieldPolymerWeightℂ_analyticAt a (ω i) hwpi)

/-- **RHS holomorphy**: on `Metric.ball 0 r` with `r ≤ π/2`, under the inflated
high-temperature window `e·(∑_P (Mr²·|tanh a|)^|P|) < 1` and a uniform ball bound
`‖Complex.tanh z‖ ≤ Mr` (`Mr ≥ 1`), `b ↦ ∑' n, fieldMayerExpansionTermℂ G n a b` is
`AnalyticOnNhd ℂ`.  Weierstrass (`Complex.differentiableOn_tsum_of_summable_norm`):
each term is analytic (`fieldMayerExpansionTermℂ_analyticOnNhd`) and the term norms are
dominated, uniformly on the ball, by the `b`-independent spanning-tree majorant at the
inflated activity `Mr²·|tanh a|` (from `norm_fieldMayerExpansionTermℂ_le_tree_activity_pow`
with `max(1, ‖Complex.tanh w‖) ≤ Mr`), summable via
`Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow`.  Field mirror
of `mayerExpansionTermComplex_tsum_differentiableOn_ball`, with the Penrose majorant. -/
theorem fieldMayerExpansionTermℂ_tsum_analyticOnNhd (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a : ℝ) {r Mr : ℝ} (hrpi : r ≤ Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr)
    (hact_star : Real.exp 1 *
      (∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card) < 1) :
    AnalyticOnNhd ℂ (fun b : ℂ => ∑' n, fieldMayerExpansionTermℂ G n a b)
      (Metric.ball 0 r) := by
  set A : ℝ := ∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card with hA
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg (fun P _ => pow_nonneg (by positivity) _)
  set u : ℕ → ℝ := fun n =>
    ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ)) * A ^ n
    with hu
  have huSummable : Summable u :=
    Penrose.summable_completeGraph_numSpanningTrees_div_factorial_mul_pow A
      (by rw [abs_of_nonneg hA_nonneg]; exact hact_star)
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r →
      ‖fieldMayerExpansionTermℂ G n a w‖ ≤ u n := by
    intro n w hw
    have hwle : ‖w‖ ≤ r := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
    have hmax : max 1 ‖Complex.tanh w‖ ≤ Mr := max_le hMr1 (hMr w hwle)
    have hmax0 : (0 : ℝ) ≤ max 1 ‖Complex.tanh w‖ := le_trans zero_le_one (le_max_left _ _)
    have ht_le : (max 1 ‖Complex.tanh w‖) ^ 2 * |Real.tanh a| ≤ Mr ^ 2 * |Real.tanh a| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmax0 hmax 2) (abs_nonneg _)
    have htnn : (0 : ℝ) ≤ (max 1 ‖Complex.tanh w‖) ^ 2 * |Real.tanh a| := by positivity
    have hsum_nn : (0 : ℝ) ≤ ∑ P ∈ allConnectedPolymers G,
        ((max 1 ‖Complex.tanh w‖) ^ 2 * |Real.tanh a|) ^ P.card :=
      Finset.sum_nonneg (fun P _ => pow_nonneg htnn _)
    have hsum_le :
        (∑ P ∈ allConnectedPolymers G,
            ((max 1 ‖Complex.tanh w‖) ^ 2 * |Real.tanh a|) ^ P.card) ≤ A := by
      rw [hA]
      exact Finset.sum_le_sum (fun P _ => pow_le_pow_left₀ htnn ht_le P.card)
    calc ‖fieldMayerExpansionTermℂ G n a w‖
        ≤ ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ))
            * (∑ P ∈ allConnectedPolymers G,
                ((max 1 ‖Complex.tanh w‖) ^ 2 * |Real.tanh a|) ^ P.card) ^ n :=
          norm_fieldMayerExpansionTermℂ_le_tree_activity_pow G n a w
      _ ≤ ((Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / (n.factorial : ℝ))
            * A ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum_nn hsum_le n) (by positivity)
      _ = u n := by rw [hu]
  have hdiff : DifferentiableOn ℂ
      (fun b : ℂ => ∑' n, fieldMayerExpansionTermℂ G n a b) (Metric.ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm huSummable
      (fun n => (fieldMayerExpansionTermℂ_analyticOnNhd G n a hrpi).differentiableOn)
      Metric.isOpen_ball hbound
  exact hdiff.analyticOnNhd Metric.isOpen_ball

/-! ## The complex `exp` identity and complex non-vanishing -/

/-- **Real-axis seed in the field direction** (GJ §17.6.1, brick 6): for fixed real `a`,
under the connected-species window `e·A_C(a) < 1` (`hact`) and the base-point
smallness `|ε_{a,0}| < 1` (`h_abs0`), the brick-5 real `exp` identity
`fieldPolymerZ G a t = Real.exp (∑' n, fieldMayerExpansionTerm G n a t)` holds for all
real `t` in a neighbourhood of `0`.  The activity hypothesis is `t`-independent; the
base-point smallness `|ε_{a,t}| < 1` holds eventually by continuity of
`t ↦ ε_{a,t}` (each factor `tanh(t)^{#odd(P)}` is continuous).  This is the *`b`-direction*
seed (fixed `a`, varying real field), distinct from the `a → 0` seed
`field_mayer_identity_general_eventually`. -/
theorem fieldPolymerZ_eq_exp_eventually_b (G : SimpleGraph ι) [Fintype G.edgeSet] (a : ℝ)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1)
    (h_abs0 : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a 0 P| < 1) :
    ∀ᶠ t : ℝ in nhds 0,
      fieldPolymerZ G a t = Real.exp (∑' n, fieldMayerExpansionTerm G n a t) := by
  have hε_cont : Continuous (fun t : ℝ =>
      ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a t P) := by
    refine continuous_finset_sum _ (fun Γ _ => continuous_finset_prod _ (fun P _ => ?_))
    simp only [fieldPolymerWeight]
    exact continuous_const.mul (continuous_real_tanh.pow _)
  have h_abs_ev : ∀ᶠ t : ℝ in nhds 0,
      |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a t P| < 1 := by
    have h := (continuous_abs.comp hε_cont).tendsto 0
    exact h.eventually_lt_const h_abs0
  filter_upwards [h_abs_ev] with t ht
  exact fieldPolymerZ_eq_exp_tsum_fieldMayerExpansionTerm G ht hact

/-- **Complex field partition `exp` identity** (GJ §17.6.1, brick 6): under
`0 < r`, `r < π/2`, the inflated window `e·(∑_P (Mr²·|tanh a|)^|P|) < 1` (`hact_star`)
with a uniform ball bound `‖Complex.tanh z‖ ≤ Mr` (`Mr ≥ 1`, `hMr`), and the base-point
smallness `|ε_{a,0}| < 1` (`h_abs0`), for all `b ∈ Metric.ball 0 r`
`fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b)`.

Analytic continuation in `b`: both sides are `AnalyticOnNhd ℂ` on the preconnected open
ball (`fieldPolymerZℂ_analyticOnNhd`, `fieldMayerExpansionTermℂ_tsum_analyticOnNhd` with
`.cexp`), and agree at the real points `t = 1/(k+1) → 0` (real-axis agreement
`fieldPolymerZℂ_ofReal` + the field seed `fieldPolymerZ_eq_exp_eventually_b`, pushed
through `Complex.ofReal_exp`/`Complex.ofReal_tsum`/`fieldMayerExpansionTermℂ_ofReal`), so
the identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` extends the
agreement to the whole ball.  Verbatim continuation skeleton of the `h = 0`
`vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex`. -/
theorem fieldPolymerZℂ_eq_exp_tsum_fieldMayerExpansionTermℂ (G : SimpleGraph ι)
    [Fintype G.edgeSet] {a r Mr : ℝ} {b : ℂ}
    (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr)
    (hact_star : Real.exp 1 *
      (∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card) < 1)
    (h_abs0 : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a 0 P| < 1)
    (hb : b ∈ Metric.ball 0 r) :
    fieldPolymerZℂ G a b = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) := by
  classical
  set f : ℂ → ℂ := fun b => fieldPolymerZℂ G a b with hf_def
  set g : ℂ → ℂ := fun b => Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) with hg_def
  set U : Set ℂ := Metric.ball (0 : ℂ) r with hU
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) r).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hr0
  -- `hact_star` implies the plain connected-species window (`Mr ≥ 1`).
  have hact : Real.exp 1 *
      (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1 := by
    refine lt_of_le_of_lt ?_ hact_star
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun P _ => ?_))
      (Real.exp_pos 1).le
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ P.card
    have : (1 : ℝ) ≤ Mr ^ 2 := one_le_pow₀ hMr1
    nlinarith [abs_nonneg (Real.tanh a)]
  -- both sides analytic on the ball
  have hf_anal : AnalyticOnNhd ℂ f U := by
    rw [hf_def, hU]; exact fieldPolymerZℂ_analyticOnNhd G a hrpi.le
  have hg_anal : AnalyticOnNhd ℂ g U := by
    rw [hg_def, hU]
    intro w hw
    exact (fieldMayerExpansionTermℂ_tsum_analyticOnNhd G a hrpi.le hMr1 hMr hact_star w hw).cexp
  -- agreement is frequent in the punctured neighbourhood of `0`
  have h_frequently : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w := by
    have h_tendsto : Filter.Tendsto (fun k : ℕ => ((1 / (k + 1 : ℝ) : ℝ) : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h_ne : ∀ k : ℕ, ((1 / (k + 1 : ℝ) : ℝ) : ℂ) ≠ 0 := fun k => by
      have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := one_div_pos.mpr (by positivity)
      exact_mod_cast hpos.ne'
    have h_principal : Filter.Tendsto (fun k : ℕ => ((1 / (k + 1 : ℝ) : ℝ) : ℂ))
        Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_tendsto, Filter.Eventually.of_forall fun k => h_ne k⟩
    have hseed := fieldPolymerZ_eq_exp_eventually_b G a hact h_abs0
    have h_eq_seq : ∀ᶠ k : ℕ in Filter.atTop,
        f ((1 / (k + 1 : ℝ) : ℝ) : ℂ) = g ((1 / (k + 1 : ℝ) : ℝ) : ℂ) := by
      have h_evseed := tendsto_one_div_add_atTop_nhds_zero_nat.eventually hseed
      filter_upwards [h_evseed] with k hk
      simp only [hf_def, hg_def]
      rw [fieldPolymerZℂ_ofReal, hk, Complex.ofReal_exp, Complex.ofReal_tsum]
      exact congrArg Complex.exp
        (tsum_congr fun n => (fieldMayerExpansionTermℂ_ofReal G n a _).symm)
    exact h_principal.frequently h_eq_seq.frequently
  -- identity theorem on the preconnected ball
  have hEqOn := hf_anal.eqOn_of_preconnected_of_frequently_eq hg_anal hUpre h0U h_frequently
  exact hEqOn hb

/-- **Complex field partition non-vanishing** (GJ §17.6.1, brick 6): under the
hypotheses of `fieldPolymerZℂ_eq_exp_tsum_fieldMayerExpansionTermℂ`, for all
`b ∈ Metric.ball 0 r`, `fieldPolymerZℂ G a b ≠ 0`.  By the `exp` identity it equals
`Complex.exp (…)`, which never vanishes (`Complex.exp_ne_zero`).  The complex
non-vanishing that brick 7's Montel/Vitali re-plumbing consumes. -/
theorem fieldPolymerZℂ_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    {a r Mr : ℝ} {b : ℂ}
    (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr)
    (hact_star : Real.exp 1 *
      (∑ P ∈ allConnectedPolymers G, (Mr ^ 2 * |Real.tanh a|) ^ P.card) < 1)
    (h_abs0 : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a 0 P| < 1)
    (hb : b ∈ Metric.ball 0 r) :
    fieldPolymerZℂ G a b ≠ 0 := by
  rw [fieldPolymerZℂ_eq_exp_tsum_fieldMayerExpansionTermℂ G hr0 hrpi hMr1 hMr hact_star h_abs0 hb]
  exact Complex.exp_ne_zero _

end IsingModel
