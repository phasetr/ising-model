import IsingModel.ClusterExpansion.FieldMayerTermPerOrderBound

/-!
# Coupling-complexified holomorphic field Mayer tower
(GJ §17.6.1, field cluster expansion, brick F2-pre)

Brick F2-pre of the minimal (pair-only) field cluster-expansion route toward
Glimm–Jaffe (GJ) *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314 (the `∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).

The complex field Mayer term `fieldMayerExpansionTermℂ G n a b`
(`FieldPolymerComplexNonvanishing.lean`) complexifies the field parameter `b` but
keeps the coupling `a` (equivalently `Real.tanh a`) *real*.  The `a`-analytic
continuation capstone F2 (real-`a` identity theorem) needs a genuine
*holomorphic-in-coupling* tower on an open complex neighbourhood, of which the
real-`a` family `{a ↦ fieldMayerExpansionTermℂ G n a b}` are the `ofReal`
restrictions.  This file builds exactly that tower: the *coupling-complexified*
field Mayer term `fieldMayerExpansionTermℂCoupling G n τ b`, obtained from
`fieldMayerExpansionTermℂ` by replacing the real fugacity `(Real.tanh a : ℂ)` with
a complex variable `τ ∈ ℂ` (the field `b ∈ ℂ` stays fixed), so each polymer weight
becomes `w_{τ,b}(P) = τ^{|P|}·(Complex.tanh b)^{#odd(P)}`.

Writing `Mr = max(1, ‖Complex.tanh b‖)` and `t_τ = Mr²·‖τ‖`, `r_τ = Δ²·e·t_τ`
(`Δ = G.maxDegree`), `ρ_τ = 8 r_τ/(1−r_τ)²`, this file supplies the five F2-pre
ingredients:

* `fieldMayerExpansionTermℂCoupling` — the coupling-complexified term (definition);
* `fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric` — the
  `‖τ‖`-geometric volume-uniform per-order bound (mirror of F1a
  `fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric` with `|tanh a| ↦ ‖τ‖`);
* `fieldMayerExpansionTermℂCoupling_summable_norm` — ball summability (mirror of F1b);
* `fieldMayerExpansionTermℂCoupling_tsum_analyticOnNhd` — holomorphy of the
  `τ`-`tsum` on a `Metric.ball 0 ρ` (each term is a finite polynomial in `τ`, hence
  entire; the geometric majorant is uniform on the ball, so Weierstrass'
  `Complex.differentiableOn_tsum_of_summable_norm` applies);
* `fieldMayerExpansionTermℂCoupling_tanh_eq` — the substitution bridge
  `fieldMayerExpansionTermℂCoupling G n (↑(Real.tanh a)) b = fieldMayerExpansionTermℂ G n a b`
  connecting F2-pre to F1's real-coupling field Mayer term.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314, and §18.4–§18.6,
  pp. 378–386 (lattice cluster expansion, analytic continuation in the fugacity).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7,
  Theorem 5.4 (Kotecký–Preiss criterion / tree-graph inequality).
- Kotecký–Preiss, Comm. Math. Phys. **103** (1986) 491–498, Theorem 1.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The coupling-complexified field Mayer term -/

/-- **Coupling-complexified field polymer weight**
`w_{τ,b}(P) = τ^{|P|}·(Complex.tanh b)^{#odd(P)}` (GJ §17.6.1, brick F2-pre).  The
coupling-complexified mirror of `fieldPolymerWeightℂ` with the *real* fugacity
`(Real.tanh a : ℂ)^{|P|}` replaced by the complex monomial `τ^{|P|}`; the field
factor `(Complex.tanh b)^{#odd(P)}` (with `#odd(P) = (oddBoundary P).card`) is kept
fixed.  Entire in `τ` (a single monomial times a `τ`-constant). -/
noncomputable def fieldPolymerWeightℂCoupling (τ b : ℂ) (P : Finset (Sym2 ι)) : ℂ :=
  τ ^ P.card * (Complex.tanh b) ^ (oddBoundary P).card

/-- **`Mr²`-inflated pointwise majorant of the coupling-complexified field weight**
(GJ §17.6.1, brick F2-pre).  With `Mr = max(1, ‖Complex.tanh b‖)`,
`‖fieldPolymerWeightℂCoupling τ b P‖ ≤ (Mr²·‖τ‖)^{|P|}`: the norm distributes over the
product/powers, and the field factor is inflated by `Mr² ≥ 1` via the parity bound
`oddBoundary_card_le_two_mul_card`.  Coupling mirror of `norm_fieldPolymerWeightℂ_le`,
with `|Real.tanh a| ↦ ‖τ‖`. -/
theorem norm_fieldPolymerWeightℂCoupling_le (τ b : ℂ) (P : Finset (Sym2 ι)) :
    ‖fieldPolymerWeightℂCoupling τ b P‖ ≤
      ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖) ^ P.card := by
  set M := max 1 ‖Complex.tanh b‖ with hM
  calc ‖fieldPolymerWeightℂCoupling τ b P‖
      = ‖τ‖ ^ P.card * ‖Complex.tanh b‖ ^ (oddBoundary P).card := by
        unfold fieldPolymerWeightℂCoupling
        rw [norm_mul, norm_pow, norm_pow]
    _ ≤ ‖τ‖ ^ P.card * (M ^ 2) ^ P.card := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
        calc ‖Complex.tanh b‖ ^ (oddBoundary P).card
            ≤ M ^ (oddBoundary P).card :=
              pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
          _ ≤ M ^ (2 * P.card) :=
              pow_le_pow_right₀ (le_max_left _ _) (oddBoundary_card_le_two_mul_card P)
          _ = (M ^ 2) ^ P.card := by rw [pow_mul]
    _ = (M ^ 2 * ‖τ‖) ^ P.card := by rw [mul_pow]; ring

/-- **Coupling-complexified field cluster-sequence activity** `∏ᵢ w_{τ,b}(ω i)`
(GJ §17.6.1, brick F2-pre).  For a cluster sequence `ω : Fin n → Finset (Sym2 ι)`
the activity factor is the multiplicative product of the coupling-complexified
weights `fieldPolymerWeightℂCoupling τ b`; coupling mirror of
`fieldClusterSeqActivityℂ`. -/
noncomputable def fieldClusterSeqActivityℂCoupling (τ b : ℂ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) : ℂ :=
  ∏ i : Fin n, fieldPolymerWeightℂCoupling τ b (ω i)

/-- **`Mr²`-inflated norm bound of the coupling-complexified field activity**
(GJ §17.6.1, brick F2-pre).  With `Mr = max(1, ‖Complex.tanh b‖)`,
`‖fieldClusterSeqActivityℂCoupling τ b ω‖ ≤ clusterSeqActivity (Mr²·‖τ‖) ω`; the norm
distributes over the product (`norm_prod_le`) and factorwise
`norm_fieldPolymerWeightℂCoupling_le`.  Coupling mirror of
`norm_fieldClusterSeqActivityℂ_le`. -/
theorem norm_fieldClusterSeqActivityℂCoupling_le (τ b : ℂ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) :
    ‖fieldClusterSeqActivityℂCoupling τ b ω‖
      ≤ clusterSeqActivity ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖) ω := by
  rw [fieldClusterSeqActivityℂCoupling, clusterSeqActivity]
  calc ‖∏ i, fieldPolymerWeightℂCoupling τ b (ω i)‖
      ≤ ∏ i, ‖fieldPolymerWeightℂCoupling τ b (ω i)‖ := norm_prod_le _ _
    _ ≤ ∏ i, ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖) ^ (ω i).card :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_fieldPolymerWeightℂCoupling_le τ b (ω i))

/-- **Coupling-complexified field Mayer expansion `n`-th term**
`∑_ω (ϕ^T(ω) : ℂ)·∏ᵢ w_{τ,b}(ω i)` (GJ §17.6.1, brick F2-pre, item 1).  The
weight-agnostic Ursell coefficient `ursellCoefficient` is reused verbatim and cast
to `ℂ`; the reference universe is the connected species `allConnectedPolymers G`, and
the activity factor is `fieldClusterSeqActivityℂCoupling`.  Coupling-complexified
mirror of `fieldMayerExpansionTermℂ` (coupling `τ ∈ ℂ`, field `b ∈ ℂ` fixed); a finite
polynomial in `τ`, hence entire. -/
noncomputable def fieldMayerExpansionTermℂCoupling (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (τ b : ℂ) : ℂ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
    (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂCoupling τ b ω

/-- **The `n = 0` coupling-complexified field Mayer term vanishes**:
`fieldMayerExpansionTermℂCoupling G 0 τ b = 0` (GJ §17.6.1, brick F2-pre).  The unique
`ω : Fin 0 → Finset (Sym2 ι)` is the empty function; the incompatibility graph on
`Fin 0` is disconnected, so `ursellCoefficient empty = 0` and its complex cast is `0`.
Coupling mirror of `fieldMayerExpansionTermℂ_zero`. -/
theorem fieldMayerExpansionTermℂCoupling_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (τ b : ℂ) : fieldMayerExpansionTermℂCoupling G 0 τ b = 0 := by
  unfold fieldMayerExpansionTermℂCoupling
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  refine mul_eq_zero.mpr (Or.inl ?_)
  rw [Complex.ofReal_eq_zero]
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h
  exact h.nonempty.elim Fin.elim0

/-- **Coupling-substitution bridge** (GJ §17.6.1, brick F2-pre, item 5).  For every
`a ∈ ℝ` and `n`,
`fieldMayerExpansionTermℂCoupling G n (↑(Real.tanh a)) b = fieldMayerExpansionTermℂ G n a b`:
substituting the complex coupling `τ = ↑(Real.tanh a)` turns the weight `τ^{|P|}` back
into `(Real.tanh a : ℂ)^{|P|}`, and the field factors coincide definitionally.  This
connects F2-pre to F1's real-coupling field Mayer term. -/
theorem fieldMayerExpansionTermℂCoupling_tanh_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂCoupling G n (Real.tanh a : ℂ) b
      = fieldMayerExpansionTermℂ G n a b := by
  unfold fieldMayerExpansionTermℂCoupling fieldMayerExpansionTermℂ
    fieldClusterSeqActivityℂCoupling fieldClusterSeqActivityℂ
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  refine congrArg _ (Finset.prod_congr rfl (fun i _ => ?_))
  rfl

/-! ## The `‖τ‖`-geometric per-order bound and summability (F1a/F1b mirror) -/

/-- **Coupling term bounded by the incompatibility-graph tree sum of activities**
(GJ §17.6.1, brick F2-pre, tree-sum base form).  At the inflated activity
`t_τ = (max 1 ‖Complex.tanh b‖)²·‖τ‖`,
`‖fieldMayerExpansionTermℂCoupling G n τ b‖ ≤ (n!)⁻¹·∑_ω ∑_{T tree of incompat(ω)}
  ∏_i t_τ^{|ω i|}`.  Combines the triangle inequality, the weight-agnostic Ursell tree
bound `ursellCoefficient_abs_le_numSpanningTrees_div_factorial`, and the activity bound
`norm_fieldClusterSeqActivityℂCoupling_le`.  Coupling mirror of
`fieldMayerExpansionTermℂ_norm_le_treeSum_activity`, with `|tanh a| ↦ ‖τ‖`. -/
theorem fieldMayerExpansionTermℂCoupling_norm_le_treeSum_activity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (τ b : ℂ) :
    ‖fieldMayerExpansionTermℂCoupling G n τ b‖ ≤
      ((n.factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            ∏ i : Fin n,
              ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖) ^ (ω i).card := by
  set t : ℝ := (max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖ with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have htri : ‖fieldMayerExpansionTermℂCoupling G n τ b‖ ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂCoupling τ b ω‖ := by
    unfold fieldMayerExpansionTermℂCoupling
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun ω _ => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine htri.trans ?_
  have hpw : ∀ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
      |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂCoupling τ b ω‖
        ≤ ((n.factorial : ℝ)⁻¹)
            * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
                ∏ i : Fin n, t ^ (ω i).card := by
    intro ω _
    have hact : ‖fieldClusterSeqActivityℂCoupling τ b ω‖ ≤ ∏ i : Fin n, t ^ (ω i).card := by
      have h := norm_fieldClusterSeqActivityℂCoupling_le τ b ω
      rwa [clusterSeqActivity, ← ht] at h
    have hprodnn : 0 ≤ ∏ i : Fin n, t ^ (ω i).card :=
      Finset.prod_nonneg (fun i _ => pow_nonneg htnn _)
    calc |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂCoupling τ b ω‖
        ≤ |ursellCoefficient ω| * ∏ i : Fin n, t ^ (ω i).card :=
          mul_le_mul_of_nonneg_left hact (abs_nonneg _)
      _ ≤ ((Penrose.numSpanningTrees (polymerSeqIncompatibilityGraph ω) : ℝ) / n.factorial)
            * ∏ i : Fin n, t ^ (ω i).card :=
          mul_le_mul_of_nonneg_right
            (ursellCoefficient_abs_le_numSpanningTrees_div_factorial ω) hprodnn
      _ = ((n.factorial : ℝ)⁻¹)
            * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
                ∏ i : Fin n, t ^ (ω i).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Penrose.numSpanningTrees]; ring
  refine (Finset.sum_le_sum hpw).trans_eq ?_
  rw [Finset.mul_sum]

/-- **Inserting the Kotecký–Preiss `e`-weights into the coupling tree-sum bound**
(GJ §17.6.1, brick F2-pre, rooted form).  Splitting off the root vertex `0` and inserting
`e^{|ω (succ i)|} ≥ 1` on the non-root factors, at the inflated activity
`t_τ = (max 1 ‖Complex.tanh b‖)²·‖τ‖` (with an outer `|·|` matching the abstract
peel-bound bridge):
`‖fieldMayerExpansionTermℂCoupling G (n+1) τ b‖ ≤ ((n+1)!)⁻¹·∑_ω ∑_{T} |t_τ|^{|ω 0|}·
  ∏_i e^{|ω (succ i)|}·|t_τ|^{|ω (succ i)|}`.  Coupling mirror of
`fieldMayerExpansionTermℂ_succ_norm_le_treeSum_rootedExpActivity`. -/
theorem fieldMayerExpansionTermℂCoupling_succ_norm_le_treeSum_rootedExpActivity
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (τ b : ℂ) :
    ‖fieldMayerExpansionTermℂCoupling G (n + 1) τ b‖ ≤
      (((n + 1).factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            (abs ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) ^ (ω 0).card *
              ∏ i : Fin n,
                Real.exp 1 ^ (ω (Fin.succ i)).card *
                  (abs ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖))
                    ^ (ω (Fin.succ i)).card := by
  have htnn : (0 : ℝ) ≤ (max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖ := by positivity
  have habs : abs ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)
      = (max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖ := abs_of_nonneg htnn
  rw [habs]
  refine (fieldMayerExpansionTermℂCoupling_norm_le_treeSum_activity G (n + 1) τ b).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun ω _ => ?_
  refine Finset.sum_le_sum fun T _ => ?_
  rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  refine le_mul_of_one_le_left (by positivity) ?_
  exact one_le_pow₀ (Real.one_le_exp_iff.mpr zero_le_one)

/-- **Volume-uniform `‖τ‖`-geometric per-order bound for the coupling field Mayer term**
(GJ §17.6.1, brick F2-pre, item 2).  With `t_τ = (max 1 ‖Complex.tanh b‖)²·‖τ‖`,
`Δ = G.maxDegree`, and `r_τ = Δ²·e·t_τ`, under the degree window `hkp : r_τ < 1`,
`‖fieldMayerExpansionTermℂCoupling G (n+1) τ b‖ ≤ |ι|/(1−r_τ)·(8 r_τ/(1−r_τ)²)ⁿ`,
volume-uniform per site.  Feeds the connected-gas instance, the support hypothesis at
`c = 2`, and the coupling tree-sum bridge into the abstract peel/geometric-closing chain
(`c = 2` ratio `ρ_τ = 8 r_τ/(1−r_τ)²`).  Coupling mirror of F1a
`fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric`, with `|tanh a| ↦ ‖τ‖`. -/
theorem fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ) (τ b : ℂ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) < 1) :
    ‖fieldMayerExpansionTermℂCoupling G (n + 1) τ b‖ ≤
      (Fintype.card ι : ℝ) /
          (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)))
        * (8 * ((G.maxDegree : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)))
            / (1 - (G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖))) ^ 2) ^ n := by
  have htnn : (0 : ℝ) ≤ (max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖ := by positivity
  have habs : abs ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)
      = (max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖ := abs_of_nonneg htnn
  have hkp' : (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * abs ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) < 1 := by
    rw [habs]; exact hkp
  have hsupp : ∀ P ∈ allConnectedPolymers G,
      ((polymerSupport P).card : ℝ) ≤ 2 * (P.card : ℝ) := fun P hP =>
    polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers G hP
  have hbridge := fieldMayerExpansionTermℂCoupling_succ_norm_le_treeSum_rootedExpActivity G n τ b
  refine (le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum G
    (connectedPolymerGasData G) n hsupp (by norm_num) hbridge hkp').trans ?_
  refine (mul_le_mul_of_nonneg_left
    (sum_pow_rootedGasParentActivePeelBound_le G (connectedPolymerGasData G) 2 (by norm_num) n hkp')
    (by positivity)).trans ?_
  rw [habs]
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  have hfact : ((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2ne : (q ^ 2) ^ n ≠ 0 := by positivity
  have hq2 : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by rw [pow_succ, pow_mul]
  have h8 : (8 : ℝ) ^ n = 2 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have hrhs : (8 * rr / q ^ 2) ^ n = 2 ^ n * 4 ^ n * rr ^ n / (q ^ 2) ^ n := by
    rw [div_pow, mul_pow, h8]
  have hgoal_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / q * (8 * rr / q ^ 2) ^ n := by
    positivity
  have hLHS : ((n + 1).factorial : ℝ)⁻¹
        * ((rr ^ n * 2 ^ n * (Fintype.card ι : ℝ) * 4 ^ n * (n.factorial : ℝ))
            / q ^ (2 * n + 1))
      = (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
          * ((Fintype.card ι : ℝ) / q * (8 * rr / q ^ 2) ^ n) := by
    rw [hrhs, hq2]
    field_simp
  rw [hLHS]
  calc (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
        * ((Fintype.card ι : ℝ) / q * (8 * rr / q ^ 2) ^ n)
      ≤ 1 * ((Fintype.card ι : ℝ) / q * (8 * rr / q ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_right hfact hgoal_nonneg
    _ = (Fintype.card ι : ℝ) / q * (8 * rr / q ^ 2) ^ n := one_mul _

/-- **Ball summability of the shifted coupling field Mayer expansion norms**
(GJ §17.6.1, brick F2-pre, item 3, shifted form).  Under the degree window
`r_τ = Δ²·e·(Mr²·‖τ‖) < 1` (`hkp`) and `ρ_τ = 8 r_τ/(1−r_τ)² < 1` (`hρ`), the map
`n ↦ ‖fieldMayerExpansionTermℂCoupling G (n+1) τ b‖` is summable, by geometric comparison
with `|ι|/(1−r_τ)·ρ_τⁿ`
(`fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric`).  Coupling mirror
of `summable_norm_fieldMayerExpansionTermℂ_succ_of_tail_condition`. -/
theorem summable_norm_fieldMayerExpansionTermℂCoupling_succ (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {τ b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖))) ^ 2 < 1) :
    Summable fun n : ℕ => ‖fieldMayerExpansionTermℂCoupling G (n + 1) τ b‖ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 8 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hgeo : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
  exact fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric G n τ b hkp

/-- **Ball summability of the full coupling field Mayer expansion norms**
(GJ §17.6.1, brick F2-pre, item 3).  Under the same degree window, the full series
`n ↦ ‖fieldMayerExpansionTermℂCoupling G n τ b‖` (including the vanishing `n = 0` head
term, `fieldMayerExpansionTermℂCoupling_zero`) is summable via `summable_nat_add_iff 1`.
Coupling mirror of `summable_norm_fieldMayerExpansionTermℂ_of_tail_condition`. -/
theorem fieldMayerExpansionTermℂCoupling_summable_norm (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {τ b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖τ‖))) ^ 2 < 1) :
    Summable fun n : ℕ => ‖fieldMayerExpansionTermℂCoupling G n τ b‖ :=
  (summable_nat_add_iff 1).mp
    (summable_norm_fieldMayerExpansionTermℂCoupling_succ G hkp hρ)

/-! ## Entirety of each term and holomorphy of the `τ`-`tsum` -/

/-- **The coupling field activity is entire in `τ`** (GJ §17.6.1, brick F2-pre): the
finite product `τ ↦ ∏ i, τ^{|ω i|}·(Complex.tanh b)^{#odd}` of `τ`-monomials times
`τ`-constants is `Differentiable ℂ`.  Coupling mirror of
`clusterSeqActivityComplex_differentiable`. -/
theorem fieldClusterSeqActivityℂCoupling_differentiable (b : ℂ) {n : ℕ}
    (ω : Fin n → Finset (Sym2 ι)) :
    Differentiable ℂ (fun τ : ℂ => fieldClusterSeqActivityℂCoupling τ b ω) := by
  unfold fieldClusterSeqActivityℂCoupling
  refine Differentiable.fun_finset_prod (fun i _ => ?_)
  unfold fieldPolymerWeightℂCoupling
  exact ((differentiable_id (𝕜 := ℂ)).pow _).mul_const _

/-- **The coupling field Mayer `n`-th term is entire in `τ`** (GJ §17.6.1, brick F2-pre):
each term is a finite polynomial in `τ` (constant Ursell coefficients times the
`τ`-entire activity), hence `Differentiable ℂ`.  Coupling mirror of
`mayerExpansionTermComplex_differentiable`. -/
theorem fieldMayerExpansionTermℂCoupling_differentiable (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (b : ℂ) :
    Differentiable ℂ (fun τ : ℂ => fieldMayerExpansionTermℂCoupling G n τ b) := by
  unfold fieldMayerExpansionTermℂCoupling
  refine Differentiable.fun_sum (fun ω _ => ?_)
  exact (fieldClusterSeqActivityℂCoupling_differentiable b ω).const_mul _

/-- **Holomorphy of the coupling `τ`-`tsum`** (GJ §17.6.1, brick F2-pre, item 4).  On
`Metric.ball 0 ρ`, under the degree window at the boundary radius `ρ` —
`r_ρ = Δ²·e·(Mr²·ρ) < 1` (`hkp`) and `ρ_ρ = 8 r_ρ/(1−r_ρ)² < 1` (`hρwin`) — the map
`τ ↦ ∑' n, fieldMayerExpansionTermℂCoupling G n τ b` is `AnalyticOnNhd ℂ`.  Each term is a
finite polynomial in `τ` (`fieldMayerExpansionTermℂCoupling_differentiable`), hence entire;
the `‖τ‖`-geometric per-order bound
(`fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric`) is dominated,
uniformly on the ball, by the fixed geometric majorant `|ι|/(1−r_ρ)·ρ_ρ^{n−1}` (`r_τ`,
`ρ_τ` are monotone in `‖τ‖ ≤ ρ`), summable since `ρ_ρ < 1`.  Weierstrass
`Complex.differentiableOn_tsum_of_summable_norm` then makes the `tsum` holomorphic on the
ball, upgraded to `AnalyticOnNhd ℂ` by `DifferentiableOn.analyticOnNhd`.  Coupling mirror
of `fieldMayerExpansionTermℂ_tsum_analyticOnNhd` (with the geometric majorant). -/
theorem fieldMayerExpansionTermℂCoupling_tsum_analyticOnNhd (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (b : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    AnalyticOnNhd ℂ (fun τ : ℂ => ∑' n, fieldMayerExpansionTermℂCoupling G n τ b)
      (Metric.ball 0 ρ) := by
  set rρ : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) with hrρ
  set q : ℝ := 1 - rρ with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrρnn : 0 ≤ rρ := by
    rw [hrρ]
    exact mul_nonneg (by positivity)
      (mul_nonneg (Real.exp_pos 1).le (mul_nonneg (by positivity) hρ0.le))
  set ρ0 : ℝ := 8 * rρ / q ^ 2 with hρ0def
  have hρ0nn : 0 ≤ ρ0 := by rw [hρ0def]; positivity
  set u : ℕ → ℝ := fun n => (Fintype.card ι : ℝ) / q * ρ0 ^ (n - 1) with hu
  have hunn : ∀ m, 0 ≤ u m := fun m => by rw [hu]; positivity
  -- Summability of the fixed geometric majorant.
  have husum : Summable u := by
    refine (summable_nat_add_iff 1).mp ?_
    have hcongr : (fun k : ℕ => u (k + 1))
        = fun k : ℕ => (Fintype.card ι : ℝ) / q * ρ0 ^ k := by
      funext k; rw [hu]; simp
    rw [hcongr]
    exact (summable_geometric_of_lt_one hρ0nn hρwin).mul_left _
  -- Uniform-on-ball domination of each term by the majorant.
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) ρ →
      ‖fieldMayerExpansionTermℂCoupling G n w b‖ ≤ u n := by
    intro n w hw
    have hwlt : ‖w‖ < ρ := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    set rw_ : ℝ := (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ‖w‖)) with hrw
    have hrwnn : 0 ≤ rw_ := by
      rw [hrw]
      exact mul_nonneg (by positivity)
        (mul_nonneg (Real.exp_pos 1).le (mul_nonneg (by positivity) (norm_nonneg _)))
    have hle : rw_ ≤ rρ := by rw [hrw, hrρ]; gcongr
    have hkpw : rw_ < 1 := lt_of_le_of_lt hle hkp
    rcases n with _ | k
    · rw [fieldMayerExpansionTermℂCoupling_zero, norm_zero]; exact hunn 0
    · have hgeo := fieldMayerExpansionTermℂCoupling_succ_norm_le_card_div_mul_geometric G k w b hkpw
      rw [← hrw] at hgeo
      refine hgeo.trans ?_
      have hqw : 0 < 1 - rw_ := by linarith [hkpw]
      have hden : q ≤ 1 - rw_ := by rw [hq]; linarith [hle]
      have hρw : (0 : ℝ) ≤ 8 * rw_ / (1 - rw_) ^ 2 := by positivity
      have hρwle : 8 * rw_ / (1 - rw_) ^ 2 ≤ ρ0 := by
        rw [hρ0def]
        gcongr
      have hpow : (8 * rw_ / (1 - rw_) ^ 2) ^ k ≤ ρ0 ^ k :=
        pow_le_pow_left₀ hρw hρwle k
      have hcard : (Fintype.card ι : ℝ) / (1 - rw_) ≤ (Fintype.card ι : ℝ) / q := by
        gcongr
      have hunk : u (k + 1) = (Fintype.card ι : ℝ) / q * ρ0 ^ k := by
        rw [hu]; simp
      rw [hunk]
      calc (Fintype.card ι : ℝ) / (1 - rw_) * (8 * rw_ / (1 - rw_) ^ 2) ^ k
          ≤ (Fintype.card ι : ℝ) / q * (8 * rw_ / (1 - rw_) ^ 2) ^ k :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ (Fintype.card ι : ℝ) / q * ρ0 ^ k :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hdiff : DifferentiableOn ℂ
      (fun τ : ℂ => ∑' n, fieldMayerExpansionTermℂCoupling G n τ b) (Metric.ball 0 ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm husum
      (fun n => (fieldMayerExpansionTermℂCoupling_differentiable G n b).differentiableOn)
      Metric.isOpen_ball hbound
  exact hdiff.analyticOnNhd Metric.isOpen_ball

end IsingModel
