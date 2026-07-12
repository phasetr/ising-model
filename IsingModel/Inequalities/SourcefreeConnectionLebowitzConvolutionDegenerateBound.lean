import IsingModel.Inequalities.SourcefreeConnectionLebowitzConvolutionBound
import IsingModel.Inequalities.GKS

/-!
# Degenerate closure of the OZ convolution bound (Stage M2, brick B1)

This file discharges the **degenerate collar** of Stage M2 of the Ornstein–Zernike
(OZ) programme for Glimm–Jaffe Theorem 17.5.1 (§17.5, p. 312; the
lower-semicontinuous / continuity half of the mass gap), issue #4386, thread
#4418, group 1a (OZ-authorised lsc programme).  Math-before-code note:
`.self-local/tex/rc-oz-lemma51-M2-convolution-estimate.tex` (brick **B1**).

## What B1 is (and is not)

Stage M1 (`Current.log_correlation_beta_deriv_le_convolution`,
`SourcefreeConnectionLebowitzConvolutionBound.lean`) is the merged, axiom-free
upper bound `∂_β log⟨σ_xσ_y⟩ ≤ ∑_e lebowitzEdgeBound e`.  Stage M2 is the linear
closure `∑_e lebowitzEdgeBound e ≤ K·d(x,y)`, split along the piecewise definition
of `Current.lebowitzEdgeBound` into the **degenerate** part `S_deg` (edges `e`
with `u` or `v ∈ {x,y}`, at most `deg x + deg y` of them) and the
**non-degenerate** convolution part `S_nd`.

**B1 = the degenerate part, closed WITHOUT the matched lower bound `H_low`.**  For
each degenerate edge `e = {u,v}` the piecewise summand is the two-point
`J⟨σ_{{u,v}△{x,y}}⟩/⟨σ_xσ_y⟩`.  Second Griffiths (GKS-II, `gks_second`) applied to
the subsets `{u,v}` and `{u,v}△{x,y}` — whose symmetric difference is `{x,y}` by
`{u,v}△({u,v}△{x,y}) = {x,y}` — gives
`⟨σ_{u,v}⟩·⟨σ_{{u,v}△{x,y}}⟩ ≤ ⟨σ_xσ_y⟩`, and the single-edge `tanh` lower bound
`⟨σ_{u,v}⟩ ≥ tanh(βJ)` (hypothesis `hedge`, brick B0) then collapses each summand
to the constant `J/tanh(βJ)`.  Summing over the `≤ deg x + deg y` degenerate edges
closes `S_deg ≤ (deg x + deg y)·J/tanh(βJ)·d(x,y)`.

This is a genuine **over-estimation correction**: the M1 docstring's implicit
"`⟨σ_wσ_y⟩/⟨σ_xσ_y⟩ ∼ e^{±m} = O(1)` per degenerate edge" is *not* justified by the
merged upper/easy-lower two-point rates alone (they are `log(2d)` apart, so a
literal read blows up like `(2d)^{d(x,y)}`); the purely algebraic GKS-II route here
avoids that blow-up and needs **no** `H_low`.

**B1 does NOT close M2.**  What remains open is the non-degenerate convolution sum
`S_nd`, whose closure genuinely needs:
* **B2** — the geodesic-tube geometric sum `∑_e ρ_+^{2ℓ(e)} ≤ C·d(x,y)` (pure `ℤ^d`
  combinatorics + mathlib, closes on merged infra);
* **B3** — the `H_low`-gated non-degenerate reduction (axiom-free because `H_low`
  is a hypothesis);
* **B4** — the genuine OZ wall: discharging the sharp *matched* two-point lower
  bound `H_low` (`⟨σ_0σ_z⟩ ≥ c·ρ^{d(0,z)}` at rate `ρ ≥ 2d·tanh(βJ)`), the OZ
  bubble / FFS Ch. 12 backbone-tail; *not* in the repository and *not* in
  Aizenman 1982, a from-scratch multi-session build requiring author
  authorisation.

The capstone chain is `B1 + B2 + B3 + B4(H_low) → M2 → hLogLip → §17.5.1 lsc`
(explicitly tracked; B4 is the load-bearing OZ core).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1,
p. 312; §17.5 pp. 304–306 (GKS-II geodesic lower bound); Friedli–Velenik,
Theorem 3.49 (GKS-II); Fernández–Fröhlich–Sokal, *Random Walks…* (1992), Ch. 12
(backbone-tail, the B4 wall).

## Main results

* `Current.lebowitzEdgeBoundFun_degenerate_le` — per (degenerate) edge:
  `lebowitzEdgeBoundFun ≤ J/tanh(βJ)` via GKS-II + the single-edge `tanh` bound.
* `Current.lebowitz_degenerate_edge_sum_le` — the degenerate-edge sum bound
  `S_deg ≤ (deg x + deg y)·(J/tanh(βJ))`.
* `Current.lebowitz_degenerate_edge_sum_le_dist` — the M2-facing form
  `S_deg ≤ (deg x + deg y)·(J/tanh(βJ))·d` for any abstract `d ≥ 1` (the intended
  instance is the graph distance `d(x,y) ≥ 1`; note that in a bare `SimpleGraph`
  `x ≠ y` alone does *not* force `SimpleGraph.dist x y ≥ 1` — non-reachable
  distinct vertices have junk `dist = 0` — but `hpos : 0 < ⟨σ_xσ_y⟩` at zero field
  forces `x, y` into one connected component (reachability), whence `dist ≥ 1`).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*}

open scoped symmDiff

/-- **Per-edge degenerate closure** (brick B1, over-estimation correction).  For a
**degenerate** edge with endpoints `u, v` (i.e. `¬ Disjoint {u,v} {x,y}`), the
Route-B per-edge bound collapses to the constant `J/tanh(βJ)`:
\[
  \mathrm{lebowitzEdgeBoundFun}(u,v)
    = J\frac{\langle\sigma_{\{u,v\}\triangle\{x,y\}}\rangle}{\langle\sigma_x\sigma_y\rangle}
    \le \frac{J}{\tanh(\beta J)} .
\]
Proof: GKS-II (`gks_second`) on `{u,v}` and `{u,v}△{x,y}` gives, via
`{u,v}△({u,v}△{x,y}) = {x,y}`, the bound
`⟨σ_{u,v}⟩·⟨σ_{{u,v}△{x,y}}⟩ ≤ ⟨σ_xσ_y⟩`; with the single-edge lower bound
`hedge : tanh(βJ) ≤ ⟨σ_{u,v}⟩` (brick B0) and GKS-I nonnegativity of
`⟨σ_{{u,v}△{x,y}}⟩` this yields
`⟨σ_{{u,v}△{x,y}}⟩/⟨σ_xσ_y⟩ ≤ 1/tanh(βJ)`.  No matched lower bound `H_low` is
used.  (Glimm–Jaffe §17.5 p. 312.) -/
theorem Current.lebowitzEdgeBoundFun_degenerate_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (htanh : 0 < Real.tanh (β * J)) {x y u v : ↑Λ}
    (hdeg : ¬ Disjoint ({u, v} : Finset ↑Λ) {x, y})
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y})
    (hedge : Real.tanh (β * J)
      ≤ correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v}) :
    Current.lebowitzEdgeBoundFun G Λ J β x y u v ≤ J / Real.tanh (β * J) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  unfold Current.lebowitzEdgeBoundFun
  rw [if_neg hdeg]
  set cXY := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} with hcXY
  set cC := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
    (symmDiff ({u, v} : Finset ↑Λ) {x, y}) with hcC
  set cUV := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v} with hcUV
  -- GKS-II on `{u,v}` and `{u,v}△{x,y}`, with `{u,v}△({u,v}△{x,y}) = {x,y}`.
  have hgks : cUV * cC ≤ cXY := by
    have h := gks_second (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) hf
      ({u, v} : Finset ↑Λ) (symmDiff ({u, v} : Finset ↑Λ) {x, y})
    rwa [symmDiff_symmDiff_cancel_left] at h
  -- GKS-I nonnegativity of the numerator two-point.
  have hcC_nn : 0 ≤ cC :=
    gks_first (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) hf
      (symmDiff ({u, v} : Finset ↑Λ) {x, y})
  -- `tanh · cC ≤ cUV · cC ≤ cXY`.
  have h1 : Real.tanh (β * J) * cC ≤ cXY :=
    le_trans (mul_le_mul_of_nonneg_right hedge hcC_nn) hgks
  rw [div_le_div_iff₀ hpos htanh]
  nlinarith [mul_le_mul_of_nonneg_left h1 hJ, hJ, h1]

/-- **Degenerate-edge sum bound** (brick B1).  For distinct `x, y ∈ Λ`, zero field,
`0 ≤ J`, `0 < β`, `0 < tanh(βJ)` (i.e. `0 < βJ`), `hpos : 0 < ⟨σ_xσ_y⟩`, and the
single-edge lower bound `hedge` (brick B0), the sum of `Current.lebowitzEdgeBound`
over the **degenerate** edges — those `e` with `x ∈ e` or `y ∈ e`, equivalently
`{u,v} ∩ {x,y} ≠ ∅` — is bounded by
\[
  S_{\mathrm{deg}} = \sum_{e:\ x\in e\ \lor\ y\in e}\mathrm{lebowitzEdgeBound}(e)
    \ \le\ (\deg x + \deg y)\,\frac{J}{\tanh(\beta J)} .
\]
Proof: each summand is `≤ J/tanh(βJ)` by
`Current.lebowitzEdgeBoundFun_degenerate_le` (GKS-II + `hedge`, no `H_low`);
`Finset.sum_le_card_nsmul` bounds the sum by `card·J/tanh(βJ)`; the degenerate-edge
count is `≤ deg x + deg y` because those edges inject into the incidence finsets of
`x` and `y` (`incidenceFinset_eq_filter`, `card_incidenceFinset_eq_degree`).

This closes the degenerate collar of M2 **without** the matched lower bound
`H_low`; the non-degenerate convolution sum `S_nd` (bricks B2/B3/B4) remains open,
with B4 (`H_low`, FFS Ch. 12) the genuine OZ wall.  (Glimm–Jaffe §17.5 p. 312;
issue #4386.) -/
theorem Current.lebowitz_degenerate_edge_sum_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj] {x y : ↑Λ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (htanh : 0 < Real.tanh (β * J))
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y})
    (hedge : ∀ u v : ↑Λ, (inducedGraph G Λ).Adj u v →
      Real.tanh (β * J) ≤ correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v}) :
    ∑ e ∈ Finset.univ.filter (fun e : (inducedGraph G Λ).edgeSet =>
          x ∈ (e : Sym2 ↑Λ) ∨ y ∈ (e : Sym2 ↑Λ)),
        Current.lebowitzEdgeBound G Λ J β x y e
      ≤ ((inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y : ℝ)
        * (J / Real.tanh (β * J)) := by
  classical
  set s := Finset.univ.filter (fun e : (inducedGraph G Λ).edgeSet =>
    x ∈ (e : Sym2 ↑Λ) ∨ y ∈ (e : Sym2 ↑Λ)) with hs
  -- Per-edge bound: each degenerate summand is `≤ J/tanh(βJ)`.
  have hterm : ∀ e ∈ s, Current.lebowitzEdgeBound G Λ J β x y e ≤ J / Real.tanh (β * J) := by
    intro e he
    rw [hs, Finset.mem_filter] at he
    obtain ⟨_, hmem⟩ := he
    obtain ⟨u, v, hab⟩ : ∃ u v, (e : Sym2 ↑Λ) = s(u, v) :=
      Sym2.inductionOn (e : Sym2 ↑Λ) (fun u v => ⟨u, v, rfl⟩)
    have hadj : (inducedGraph G Λ).Adj u v := by
      have he2 := e.2
      rw [hab, SimpleGraph.mem_edgeSet] at he2
      exact he2
    -- Degeneracy: `x ∈ {u,v}` or `y ∈ {u,v}` contradicts disjointness from `{x,y}`.
    have hdeg : ¬ Disjoint ({u, v} : Finset ↑Λ) {x, y} := by
      rw [Finset.not_disjoint_iff]
      rw [hab, Sym2.mem_iff, Sym2.mem_iff] at hmem
      rcases hmem with (rfl | rfl) | (rfl | rfl)
      · exact ⟨x, by simp, by simp⟩
      · exact ⟨x, by simp, by simp⟩
      · exact ⟨y, by simp, by simp⟩
      · exact ⟨y, by simp, by simp⟩
    rw [Current.lebowitzEdgeBound, hab, Sym2.lift_mk]
    exact Current.lebowitzEdgeBoundFun_degenerate_le G Λ hJ hβ htanh hdeg hpos (hedge u v hadj)
  -- Count: the degenerate edges number `≤ deg x + deg y`.
  have hcard : s.card ≤ (inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y := by
    have hsub : s.image (Subtype.val) ⊆
        (inducedGraph G Λ).edgeFinset.filter (fun e => x ∈ e ∨ y ∈ e) := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨a, ha, rfl⟩ := he
      rw [hs, Finset.mem_filter] at ha
      rw [Finset.mem_filter]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr a.2, ha.2⟩
    calc s.card = (s.image (Subtype.val)).card :=
          (Finset.card_image_of_injective s Subtype.val_injective).symm
      _ ≤ ((inducedGraph G Λ).edgeFinset.filter (fun e => x ∈ e ∨ y ∈ e)).card :=
          Finset.card_le_card hsub
      _ ≤ (inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y := by
          rw [Finset.filter_or]
          refine le_trans (Finset.card_union_le _ _) (le_of_eq ?_)
          rw [← SimpleGraph.incidenceFinset_eq_filter, ← SimpleGraph.incidenceFinset_eq_filter,
            SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.card_incidenceFinset_eq_degree]
  -- Assemble: `∑ ≤ card • (J/tanh) = card·(J/tanh) ≤ (deg x + deg y)·(J/tanh)`.
  have hK_nn : 0 ≤ J / Real.tanh (β * J) := div_nonneg hJ htanh.le
  refine le_trans (Finset.sum_le_card_nsmul s _ (J / Real.tanh (β * J)) hterm) ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hK_nn
  calc (s.card : ℝ)
      ≤ ((inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y : ℕ) := by exact_mod_cast hcard
    _ = _ := by push_cast; ring

/-- **Degenerate-edge sum bound, M2-facing form** (brick B1).  Multiplying
`Current.lebowitz_degenerate_edge_sum_le` by any abstract `d ≥ 1` gives the
linear-in-separation shape `S_deg ≤ (deg x + deg y)·(J/tanh(βJ))·d` targeted by
Stage M2.  The intended instance is the graph distance `d(x,y) ≥ 1`; the theorem
keeps `d` abstract (`hd : 1 ≤ d`) precisely because, in a bare `SimpleGraph`,
`x ≠ y` alone does *not* give `SimpleGraph.dist x y ≥ 1` (non-reachable distinct
vertices carry the junk value `dist = 0`).  The bound `d(x,y) ≥ 1` is legitimate
here because `hpos : 0 < ⟨σ_xσ_y⟩` at zero field forces `x, y` into a single
connected component (reachability), and reachability of distinct vertices yields
`dist x y ≥ 1`.

Only the **degenerate** collar is closed here; the non-degenerate convolution part
`S_nd` (bricks B2/B3/B4, with B4 = `H_low`/FFS Ch. 12 the OZ wall) is not addressed.
(Glimm–Jaffe §17.5 p. 312; issue #4386.) -/
theorem Current.lebowitz_degenerate_edge_sum_le_dist (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    [DecidableRel (inducedGraph G Λ).Adj] {x y : ↑Λ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (htanh : 0 < Real.tanh (β * J))
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y})
    (hedge : ∀ u v : ↑Λ, (inducedGraph G Λ).Adj u v →
      Real.tanh (β * J) ≤ correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v})
    {d : ℝ} (hd : 1 ≤ d) :
    ∑ e ∈ Finset.univ.filter (fun e : (inducedGraph G Λ).edgeSet =>
          x ∈ (e : Sym2 ↑Λ) ∨ y ∈ (e : Sym2 ↑Λ)),
        Current.lebowitzEdgeBound G Λ J β x y e
      ≤ ((inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y : ℝ)
        * (J / Real.tanh (β * J)) * d := by
  refine le_trans (Current.lebowitz_degenerate_edge_sum_le G Λ hJ hβ htanh hpos hedge) ?_
  refine le_mul_of_one_le_right ?_ hd
  have hK_nn : 0 ≤ J / Real.tanh (β * J) := div_nonneg hJ htanh.le
  have hdeg_nn : (0 : ℝ) ≤ ((inducedGraph G Λ).degree x + (inducedGraph G Λ).degree y : ℝ) := by
    positivity
  exact mul_nonneg hdeg_nn hK_nn

end Ambient

end IsingModel
