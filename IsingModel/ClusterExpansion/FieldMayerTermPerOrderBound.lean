import IsingModel.ClusterExpansion.FieldPolymerComplexNonvanishing
import IsingModel.ClusterExpansion.MayerTermTailSummability
import IsingModel.ClusterExpansion.TwoPointCapstonePrereqs

/-!
# Volume-uniform per-order geometric bound for the complex field Mayer term
(GJ §17.6.1, field cluster expansion, brick F1a)

Brick F1a of the minimal (pair-only) field cluster-expansion route toward
Glimm–Jaffe (GJ) *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314 (the `∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).

The field partition function is a hard-core gas of the *connected* field polymers
`allConnectedPolymers G` (the even-degree clause of the `h = 0` gas is dropped),
with the two-factor complex activity `w^ℂ_{a,b}(P) = (tanh a)^{|P|}·(tanh_ℂ b)^{#odd(P)}`.
Writing `M = max(1, ‖Complex.tanh b‖)`, brick 5's factorwise bound
`‖w^ℂ_{a,b}(P)‖ ≤ (M²·|tanh a|)^{|P|}` inflates the coupling smallness by the bounded
single-site factor `M² ≥ 1`, so the field enters the estimate only through
`t_∗ = M²·|tanh a|`.

The R1–R3 refactor has already lifted the entire Kotecký–Preiss moment-core,
leaf-peel chain, and tree-bridge off the hardcoded even/`h = 0` gas onto an abstract
`PolymerGasData G 𝓟` with a support hypothesis `|supp P| ≤ c·|P|` (the peel bound
`sum_pow_rootedGasParentActivePeelBound_le` carries the corresponding factor `cⁿ`).
This file supplies the three connected-gas-specific ingredients:

* `connectedPolymerGasData` — the connected gas as an abstract `PolymerGasData` instance;
* `polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers` — the support hypothesis
  at `c = 2` (`|supp P| ≤ |P| + 1 ≤ 2|P|` for a nonempty connected polymer);
* the field-Mayer → Penrose-tree bridge
  (`fieldMayerExpansionTermℂ_norm_le_treeSum_activity`,
  `fieldMayerExpansionTermℂ_succ_norm_le_treeSum_rootedExpActivity`),

and, feeding these into the abstract peel/geometric-closing chain, the headline
per-order geometric bound (with the `c = 2` support constant, ρ_∗ = 8 r_∗/(1−r_∗)²):

`fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric`:
`‖fieldMayerExpansionTermℂ G (n+1) a b‖ ≤ |ι|/(1−r_∗)·(8 r_∗/(1−r_∗)²)ⁿ`,
with `r_∗ = Δ²·e·t_∗` and `Δ = G.maxDegree`, volume-uniform per site (dividing by `|ι|`
leaves a constant depending only on `Δ`, `a`, and the field ball radius through `M`).

## References
- Friedli–Velenik §5.3, Proposition 5.3, gives the formal Mayer/Ursell identity;
  §5.4, Theorem 5.4, p. 224, gives convergence.
- Kotecký–Preiss, Comm. Math. Phys. **103** (1986) 491–498, Theorem 1, supplies
  only the abstract convergence criterion; it is not the tree-bound source.
- Glimm–Jaffe §18.4, pp. 332–335, provides a continuum P(φ)₂ analogy only;
  not a lattice-Ising source. The per-order tree bound is a project extension.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **The connected gas satisfies the polymer-gas hypotheses** (GJ §17.6.1, brick F1a,
ingredient (i)).  Every member of `allConnectedPolymers G` is a nonempty edge-connected
subset of `G.edgeFinset`, so the connected field gas instantiates the abstract
`PolymerGasData` bundle that the volume-uniform Kotecký–Preiss counting/moment/peel core
consumes.  Field mirror of `evenPolymerGasData`, discharging the three fields from
`mem_allConnectedPolymers`. -/
theorem connectedPolymerGasData (G : SimpleGraph ι) [Fintype G.edgeSet] :
    PolymerGasData G (allConnectedPolymers G) where
  mem_edgeFinset _ hP := (mem_allConnectedPolymers.mp hP).subset
  connected _ hP := (mem_allConnectedPolymers.mp hP).connected
  nonempty _ hP := (mem_allConnectedPolymers.mp hP).nonempty

/-- **Connected-gas support bound at `c = 2`** (GJ §17.6.1, brick F1a, ingredient (ii)).
For a connected polymer `P ∈ allConnectedPolymers G` the vertex count is controlled by
the edge count, `(|supp P| : ℝ) ≤ 2·(|P| : ℝ)`, from `|supp P| ≤ |P| + 1`
(`polymerSupport_card_le_card_add_one_of_isEdgeConnected`) and `1 ≤ |P|` (nonemptiness).
This is exactly the support constant `c = 2` propagating into the geometric ratio
ρ_∗ = 4·c·r_∗/(1−r_∗)² = 8 r_∗/(1−r_∗)². -/
theorem polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers (G : SimpleGraph ι)
    [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : P ∈ allConnectedPolymers G) :
    ((polymerSupport P).card : ℝ) ≤ 2 * (P.card : ℝ) := by
  have hcp := mem_allConnectedPolymers.mp hP
  have h1 : (polymerSupport P).card ≤ P.card + 1 :=
    polymerSupport_card_le_card_add_one_of_isEdgeConnected G hcp.subset hcp.nonempty
      hcp.connected
  have h2 : 1 ≤ P.card := Finset.card_pos.mpr hcp.nonempty
  have h3 : (polymerSupport P).card ≤ 2 * P.card := by omega
  exact_mod_cast h3

/-- **Complex field Mayer term bounded by the incompatibility-graph tree sum of activities**
(GJ §17.6.1, brick F1a, ingredient (iii), base form).  At the inflated activity
`t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|`,
`‖fieldMayerExpansionTermℂ G n a b‖ ≤ (n!)⁻¹·∑_ω ∑_{T tree of incompat(ω)}
  ∏_i t_∗^{|ω i|}`, the sum ranging over the connected species `allConnectedPolymers G`.
Combines the triangle
inequality (`norm_sum_le`, `‖(ursell : ℂ)‖ = |ursell|`), the weight-agnostic Ursell tree
bound `ursellCoefficient_abs_le_numSpanningTrees_div_factorial` (which keeps the
incompatibility graph, not `⊤`), and the brick-5 factorwise activity bound
`norm_fieldClusterSeqActivityℂ_le`.  Field/complex mirror of
`mayerExpansionTerm_abs_le_treeSum_activity`. -/
theorem fieldMayerExpansionTermℂ_norm_le_treeSum_activity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (a : ℝ) (b : ℂ) :
    ‖fieldMayerExpansionTermℂ G n a b‖ ≤
      ((n.factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            ∏ i : Fin n,
              ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ (ω i).card := by
  set t : ℝ := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have htri : ‖fieldMayerExpansionTermℂ G n a b‖ ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
        |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖ := by
    unfold fieldMayerExpansionTermℂ
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun ω _ => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine htri.trans ?_
  have hpw : ∀ ω ∈ Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G),
      |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖
        ≤ ((n.factorial : ℝ)⁻¹)
            * ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
                ∏ i : Fin n, t ^ (ω i).card := by
    intro ω _
    have hact : ‖fieldClusterSeqActivityℂ a b ω‖ ≤ ∏ i : Fin n, t ^ (ω i).card := by
      have h := norm_fieldClusterSeqActivityℂ_le a b ω
      rwa [clusterSeqActivity, ← ht] at h
    have hprodnn : 0 ≤ ∏ i : Fin n, t ^ (ω i).card :=
      Finset.prod_nonneg (fun i _ => pow_nonneg htnn _)
    calc |ursellCoefficient ω| * ‖fieldClusterSeqActivityℂ a b ω‖
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

/-- **Inserting the Kotecký–Preiss `e`-weights into the field Mayer tree-sum bound**
(GJ §17.6.1, brick F1a, ingredient (iii), rooted form).  Splitting off the root vertex
`0` and inserting `e^{|ω (succ i)|} ≥ 1` on the non-root factors, at the inflated activity
`t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|` (written with an outer `|·|` matching the
abstract peel-bound bridge, since `t_∗ ≥ 0`):
`‖fieldMayerExpansionTermℂ G (n+1) a b‖ ≤ ((n+1)!)⁻¹·∑_ω ∑_{T tree of incompat(ω)}
  |t_∗|^{|ω 0|}·∏_i e^{|ω (succ i)|}·|t_∗|^{|ω (succ i)|}`.
The non-root factors are in the per-edge Kotecký–Preiss weight form consumed by
`le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum` (as the bridge `hbridge`).
Field/complex mirror of `mayerExpansionTerm_succ_abs_le_treeSum_rootedExpActivity`. -/
theorem fieldMayerExpansionTermℂ_succ_norm_le_treeSum_rootedExpActivity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (n : ℕ) (a : ℝ) (b : ℂ) :
    ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ ≤
      (((n + 1).factorial : ℝ)⁻¹) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G),
          ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
            (abs ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) ^ (ω 0).card *
              ∏ i : Fin n,
                Real.exp 1 ^ (ω (Fin.succ i)).card *
                  (abs ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))
                    ^ (ω (Fin.succ i)).card := by
  have htnn : (0 : ℝ) ≤ (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| := by positivity
  have habs : abs ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)
      = (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| := abs_of_nonneg htnn
  rw [habs]
  refine (fieldMayerExpansionTermℂ_norm_le_treeSum_activity G (n + 1) a b).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun ω _ => ?_
  refine Finset.sum_le_sum fun T _ => ?_
  rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  refine le_mul_of_one_le_left (by positivity) ?_
  exact one_le_pow₀ (Real.one_le_exp_iff.mpr zero_le_one)

/-- **Volume-uniform per-order geometric bound for the complex field Mayer term**
(GJ §17.6.1, brick F1a, Theorem F1a).  With `t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|`,
`Δ = G.maxDegree`, and `r_∗ = Δ²·e·t_∗`, under the degree window `hkp : r_∗ < 1`,
`‖fieldMayerExpansionTermℂ G (n+1) a b‖ ≤ |ι|/(1−r_∗)·(8 r_∗/(1−r_∗)²)ⁿ`,
volume-uniform per site.  Feeds the connected-gas instance (`connectedPolymerGasData`),
the support hypothesis at `c = 2`
(`polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers`), and the field tree-sum
bridge (`fieldMayerExpansionTermℂ_succ_norm_le_treeSum_rootedExpActivity`) into the abstract
peel/geometric-closing chain `le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum`
∘ `sum_pow_rootedGasParentActivePeelBound_le` (whose factor `cⁿ = 2ⁿ` combines with the
tree-count `4ⁿ` into `8ⁿ`), with the `((n+1)!)⁻¹·n! ≤ 1` closing.  Field/complex mirror of
`mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`, with the `c = 2` ratio. -/
theorem fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ) (a : ℝ) (b : ℂ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1) :
    ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ ≤
      (Fintype.card ι : ℝ) /
          (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        * (8 * ((G.maxDegree : ℝ) ^ 2 *
              (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
            / (1 - (G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2) ^ n := by
  have htnn : (0 : ℝ) ≤ (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| := by positivity
  have habs : abs ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)
      = (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| := abs_of_nonneg htnn
  have hkp' : (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * abs ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1 := by
    rw [habs]; exact hkp
  have hsupp : ∀ P ∈ allConnectedPolymers G,
      ((polymerSupport P).card : ℝ) ≤ 2 * (P.card : ℝ) := fun P hP =>
    polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers G hP
  have hbridge := fieldMayerExpansionTermℂ_succ_norm_le_treeSum_rootedExpActivity G n a b
  refine (le_sum_pow_rootedGasParentActivePeelBound_of_le_penroseTreeSum G
    (connectedPolymerGasData G) n hsupp (by norm_num) hbridge hkp').trans ?_
  refine (mul_le_mul_of_nonneg_left
    (sum_pow_rootedGasParentActivePeelBound_le G (connectedPolymerGasData G) 2 (by norm_num) n hkp')
    (by positivity)).trans ?_
  rw [habs]
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) with hrr
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

/-- **The `n = 0` complex field Mayer term vanishes**: `fieldMayerExpansionTermℂ G 0 a b = 0`
(GJ §17.6.1, brick F1b).  The unique `ω : Fin 0 → Finset (Sym2 ι)` is the empty function; the
incompatibility graph on `Fin 0` is disconnected (`Connected` requires `Nonempty`), so
`ursellCoefficient empty = 0` and its complex cast is `0`.  Field/complex mirror of
`mayerExpansionTermComplex_zero`. -/
theorem fieldMayerExpansionTermℂ_zero (G : SimpleGraph ι) [Fintype G.edgeSet] (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂ G 0 a b = 0 := by
  unfold fieldMayerExpansionTermℂ
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  refine mul_eq_zero.mpr (Or.inl ?_)
  rw [Complex.ofReal_eq_zero]
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h
  exact h.nonempty.elim Fin.elim0

/-- **Summability of the shifted complex field Mayer expansion terms** (GJ §17.6.1, brick F1b).
Under the degree window (W) — `r_∗ = Δ²·e·t_∗ < 1` and `ρ_∗ = 8 r_∗/(1−r_∗)² < 1` at the
inflated activity `t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|` — the map
`n ↦ ‖fieldMayerExpansionTermℂ G (n+1) a b‖` is summable.  The geometric majorant
`|ι|/(1−r_∗)·ρ_∗ⁿ` (`fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric`, F1a) is
summable since its ratio `ρ_∗ < 1`.  Field/complex mirror of
`summable_norm_mayerExpansionTermComplex_succ_of_tail_condition`, with the `c = 2` ratio. -/
theorem summable_norm_fieldMayerExpansionTermℂ_succ_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    Summable fun n : ℕ => ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 8 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hgeo : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
  exact fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric G n a b hkp

/-- **Summability of the full complex field Mayer expansion terms** (GJ §17.6.1, brick F1b).
Under the same degree window, the full series `n ↦ ‖fieldMayerExpansionTermℂ G n a b‖`
(including the vanishing `n = 0` head term) is summable: `summable_nat_add_iff 1` adds the
single `n = 0` term to the summable shifted series.  Field/complex mirror of
`summable_abs_mayerExpansionTerm_of_tail_condition`. -/
theorem summable_norm_fieldMayerExpansionTermℂ_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    Summable fun n : ℕ => ‖fieldMayerExpansionTermℂ G n a b‖ :=
  (summable_nat_add_iff 1).mp
    (summable_norm_fieldMayerExpansionTermℂ_succ_of_tail_condition G hkp hρ)

/-- **Explicit bound on the shifted complex field Mayer expansion sum** (GJ §17.6.1, brick F1b,
Theorem F1b).  Summing the geometric per-order norm bound
(`fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric`, F1a) gives
`∑'_n ‖fieldMayerExpansionTermℂ G (n+1) a b‖ ≤ |ι|/((1−r_∗)(1−ρ_∗))` with `r_∗ = Δ²·e·t_∗`
and `ρ_∗ = 8 r_∗/(1−r_∗)²`, under the degree window (W).  Field/complex mirror of
`tsum_norm_mayerExpansionTermComplex_succ_le`, with the `c = 2` ratio. -/
theorem tsum_norm_fieldMayerExpansionTermℂ_succ_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    (∑' n : ℕ, ‖fieldMayerExpansionTermℂ G (n + 1) a b‖)
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 *
    (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 8 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hsummL : Summable fun n : ℕ => ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ :=
    summable_norm_fieldMayerExpansionTermℂ_succ_of_tail_condition G hkp hρ
  have hsummR : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  calc (∑' n : ℕ, ‖fieldMayerExpansionTermℂ G (n + 1) a b‖)
      ≤ ∑' n : ℕ, (Fintype.card ι : ℝ) / q * ρ ^ n :=
        hsummL.tsum_le_tsum
          (fun n => fieldMayerExpansionTermℂ_succ_norm_le_card_div_mul_geometric G n a b hkp)
          hsummR
    _ = (Fintype.card ι : ℝ) / q * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ]

/-- **Volume-uniform (per-site) bound on the shifted complex field Mayer expansion sum**
(GJ §17.6.1, brick F1b).  Dividing `tsum_norm_fieldMayerExpansionTermℂ_succ_le` by the volume
`|ι|` gives the per-site constant `((1−r_∗)(1−ρ_∗))⁻¹` (`r_∗ = Δ²·e·t_∗`,
`ρ_∗ = 8 r_∗/(1−r_∗)²`), independent of the volume.  Field/complex mirror of
`tsum_norm_mayerExpansionTermComplex_succ_div_card_le`, with the `c = 2` ratio. -/
theorem tsum_norm_fieldMayerExpansionTermℂ_succ_div_card_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    (∑' n : ℕ, ‖fieldMayerExpansionTermℂ G (n + 1) a b‖) / (Fintype.card ι : ℝ)
      ≤ ((1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2))⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard]
  refine (tsum_norm_fieldMayerExpansionTermℂ_succ_le G hkp hρ).trans (le_of_eq ?_)
  rw [mul_inv]
  ring

/-- **Volume-uniform (per-site) bound on the full complex field Mayer expansion sum**
(GJ §17.6.1, brick F1b, Theorem F1b).  Since the `n = 0` complex field Mayer term vanishes
(`fieldMayerExpansionTermℂ_zero`), the full series equals the shifted one, and
`‖∑'_n‖ ≤ ∑'_n ‖·‖` (`norm_tsum_le_tsum_norm`), so the same per-site constant
`((1−r_∗)(1−ρ_∗))⁻¹` (`r_∗ = Δ²·e·t_∗`, `ρ_∗ = 8 r_∗/(1−r_∗)²`) bounds the per-site norm of the
full field Mayer expansion sum.  Field/complex mirror of
`tsum_norm_mayerExpansionTermComplex_div_card_le`, with the `c = 2` ratio. -/
theorem tsum_norm_fieldMayerExpansionTermℂ_div_card_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Nonempty ι] {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    ‖∑' n : ℕ, fieldMayerExpansionTermℂ G n a b‖ / (Fintype.card ι : ℝ)
      ≤ ((1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2))⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsucc : Summable fun n : ℕ => ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ :=
    summable_norm_fieldMayerExpansionTermℂ_succ_of_tail_condition G hkp hρ
  have hsum : Summable fun n : ℕ => fieldMayerExpansionTermℂ G n a b :=
    (summable_nat_add_iff 1).mp hsucc.of_norm
  have hshift : (∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
      = ∑' n : ℕ, fieldMayerExpansionTermℂ G (n + 1) a b := by
    rw [hsum.tsum_eq_zero_add, fieldMayerExpansionTermℂ_zero, zero_add]
  have hnorm : ‖∑' n : ℕ, fieldMayerExpansionTermℂ G n a b‖
      ≤ ∑' n : ℕ, ‖fieldMayerExpansionTermℂ G (n + 1) a b‖ := by
    rw [hshift]
    exact norm_tsum_le_tsum_norm hsucc
  rw [div_le_iff₀ hcard]
  refine hnorm.trans ?_
  rw [← div_le_iff₀ hcard]
  exact tsum_norm_fieldMayerExpansionTermℂ_succ_div_card_le G hkp hρ

end IsingModel
