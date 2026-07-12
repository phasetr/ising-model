import IsingModel.Inequalities.SourcefreeConnectionExcessEdgeSum
import IsingModel.Inequalities.SourcefreeConnectionEdgeReachableLeg
import IsingModel.Inequalities.Lebowitz.LebowitzFour

/-!
# Route-B convolution upper bound on `∂_β log⟨σ_xσ_y⟩` (OZ Stage M1)

This file assembles **Stage M1** of the random-current build toward the
Ornstein–Zernike log-derivative estimate of Glimm–Jaffe Theorem 17.5.1
(§17.5, p. 312; the lower-semicontinuous / continuity half of the mass gap),
issue #4386, thread #4418, group 1a (OZ-authorised lsc programme).

## What M1 is (and is not)

The continuity half of Theorem 17.5.1 reduces, by the mean value theorem, to the
uniform log-Lipschitz estimate `hLogLip`, which through the merged excess-current
identity (Stage D + B1 + P1, all axiom-free) reduces to the single *upper* bound
`∂_β log⟨σ_xσ_y⟩ ≤ C·d(x,y)`.  The merged master identity is the equality
\[
  \partial_\beta\log\langle\sigma_x\sigma_y\rangle_\Lambda
    = J\sum_{e=\{u,v\}\in E}\frac{U^T_{uvxy}}{\langle\sigma_x\sigma_y\rangle},
  \qquad
  U^T_{uvxy}=\langle\sigma_u\sigma_v\sigma_x\sigma_y\rangle
      -\langle\sigma_u\sigma_v\rangle\langle\sigma_x\sigma_y\rangle .
\]
**M1 applies the tight, merged four-point Lebowitz inequality
`lebowitz_four_zero_field` to each truncated four-point** `U^T_{uvxy}`, turning
the master *equality* into the *upper bound*
\[
  \partial_\beta\log\langle\sigma_x\sigma_y\rangle
    \le \sum_{e=\{u,v\}}
      \begin{cases}
        J\dfrac{\langle\sigma_u\sigma_x\rangle\langle\sigma_v\sigma_y\rangle
          +\langle\sigma_u\sigma_y\rangle\langle\sigma_v\sigma_x\rangle}
          {\langle\sigma_x\sigma_y\rangle}
          & \{u,v\}\cap\{x,y\}=\varnothing,\\[6pt]
        J\dfrac{\langle\sigma_{\{u,v\}\triangle\{x,y\}}\rangle}
          {\langle\sigma_x\sigma_y\rangle}
          & \text{$e$ degenerate.}
      \end{cases}
\]
For a **non-degenerate** edge `U^T_{uvxy}\le\langle\sigma_u\sigma_x\rangle
\langle\sigma_v\sigma_y\rangle+\langle\sigma_u\sigma_y\rangle\langle\sigma_v\sigma_x
\rangle` (the `⟨σ_uσ_v⟩⟨σ_xσ_y⟩` diagonal pairing cancels the truncation), and
for a **degenerate** edge (`{u,v}∩{x,y}≠∅`) the identity keeps the genuine
two-point `⟨σ_{{u,v}△{x,y}}⟩` and the subtracted `⟨σ_uσ_v⟩≥0` is dropped by
GKS-I; there are only `≤ 4d` such edges, so no `|E|` term appears.

**M1 does NOT by itself discharge `hLogLip`.**  Its right-hand side is exactly the
OZ *convolution ratio*
`∑_e ⟨σ_uσ_x⟩⟨σ_vσ_y⟩/⟨σ_xσ_y⟩`, whose `≤ K·d(x,y)` closure is **gated on M2**,
the sharp *matching* two-point lower bound `⟨σ_0σ_x⟩≥c·ρ^{d}` with the same rate
as the merged upper bound (`oz-hlow-sharp-two-point-lower-bound.tex`; FFS Ch. 12
backbone-tail).  M1 is the clean outer shell reducing the target to that OZ core,
and it **discharges the earlier "crude-Lebowitz blow-up" misdiagnosis**
(`correlation_beta_deriv_le_lebowitz` bounded every degenerate summand by the
constant `1` before dividing, spuriously producing `|E|/⟨σ_xσ_y⟩ ∼ e^{+md}`; the
tight form here keeps the true two-point, `O(1)` per edge).

All correlations, weights and currents are the merged repository definitions
(`correlation`, `Current.weightSum`; FV / GJ conventions).  References:
Fernández–Fröhlich–Sokal, *Random Walks…* (1992), Ch. 12; Lebowitz four-point
inequality (`lebowitz_four_zero_field`, the corrected form of GHS/FV eq. (3.45));
Glimm–Jaffe, *Quantum Physics* 2nd ed., §17.5, Theorem 17.5.1, p. 312.

## Main results

* `Current.lebowitzEdgeBoundFun` / `Current.lebowitzEdgeBound` — the per-edge
  Route-B upper bound (piecewise: Lebowitz convolution pairing on non-degenerate
  edges, GKS-I two-point on degenerate edges).
* `Current.log_correlation_beta_deriv_le_convolution` (M1) — the assembled upper
  bound `∂_β log⟨σ_xσ_y⟩ ≤ ∑_e lebowitzEdgeBound e`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

open scoped symmDiff

/-- **Per-edge Route-B bound (curried form).**  For an ordered pair `(u, v)` of
vertices representing an edge, the Route-B upper bound on the per-edge
log-derivative contribution: the Lebowitz cross-pairing convolution
`J(⟨σ_uσ_x⟩⟨σ_vσ_y⟩+⟨σ_uσ_y⟩⟨σ_vσ_x⟩)/⟨σ_xσ_y⟩` when `{u,v}` is disjoint from
`{x,y}` (non-degenerate edge), and the GKS-I two-point
`J⟨σ_{{u,v}△{x,y}}⟩/⟨σ_xσ_y⟩` otherwise (degenerate edge, `σ²=1` collapse).
This is representative-symmetric (see `Current.lebowitzEdgeBoundFun_symm`), so it
descends to `Sym2` as `Current.lebowitzEdgeBound`. -/
noncomputable def Current.lebowitzEdgeBoundFun (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (J β : ℝ) (x y u v : ↑Λ) : ℝ :=
  if Disjoint ({u, v} : Finset ↑Λ) {x, y} then
    J * (correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, x}
          * correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {v, y}
        + correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, y}
          * correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {v, x})
      / correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
  else
    J * correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
          (symmDiff ({u, v} : Finset ↑Λ) {x, y})
      / correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}

omit [DecidableEq V] in
/-- **Representative-symmetry of the per-edge Route-B bound.**  Swapping the two
endpoints of an edge leaves `Current.lebowitzEdgeBoundFun` unchanged: the
disjointness condition and the symmetric difference depend only on the unordered
pair, and the non-degenerate branch is symmetric under `u ↔ v` (it swaps the two
cross-pairing summands and their factors). -/
theorem Current.lebowitzEdgeBoundFun_symm (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (J β : ℝ) (x y u v : ↑Λ) :
    Current.lebowitzEdgeBoundFun G Λ J β x y u v
      = Current.lebowitzEdgeBoundFun G Λ J β x y v u := by
  simp only [Current.lebowitzEdgeBoundFun, Finset.pair_comm u v]
  split_ifs with h
  · ring
  · rfl

/-- **Per-edge Route-B bound (edge form).**  The descent of
`Current.lebowitzEdgeBoundFun` to an edge `e ∈ (inducedGraph G Λ).edgeSet` via
`Sym2.lift`; well defined by `Current.lebowitzEdgeBoundFun_symm`.  This is the
summand of the Route-B convolution bound
`Current.log_correlation_beta_deriv_le_convolution`. -/
noncomputable def Current.lebowitzEdgeBound (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] (J β : ℝ) (x y : ↑Λ)
    (e : (inducedGraph G Λ).edgeSet) : ℝ :=
  Sym2.lift ⟨Current.lebowitzEdgeBoundFun G Λ J β x y,
    Current.lebowitzEdgeBoundFun_symm G Λ J β x y⟩ (e : Sym2 ↑Λ)

set_option linter.unusedDecidableInType false in
/-- **Route-B convolution upper bound on the correlation log-derivative (OZ Stage
M1).**  For `x ≠ y ∈ Λ`, `0 < β`, `0 ≤ J`, and `hpos : 0 < ⟨σ_xσ_y⟩_Λ`,
\[
  \partial_\beta\log\langle\sigma_x\sigma_y\rangle_\Lambda
    \le \sum_{e\in E}\; \mathrm{lebowitzEdgeBound}(e),
\]
where each summand is the tight Lebowitz cross-pairing convolution
`J(⟨σ_uσ_x⟩⟨σ_vσ_y⟩+⟨σ_uσ_y⟩⟨σ_vσ_x⟩)/⟨σ_xσ_y⟩` on non-degenerate edges and the
GKS-I two-point `J⟨σ_{{u,v}△{x,y}}⟩/⟨σ_xσ_y⟩` on degenerate edges (`σ²=1`
collapse).

Proof: rewrite `∂_β log⟨σ_xσ_y⟩` by the Stage-D derivative
`Current.hasDerivAt_log_correlation_beta` (`.deriv`), decompose the excess current
over edges by B1 `Current.doubledSourcefree_excess_eq_sum_edge`, distribute the
`1/(2β)` prefactor, and bound each per-edge summand.  On a **non-degenerate** edge
P1 `Current.doubledSourcefree_edgeExcess_eq_truncated4pt` rewrites the summand as
`2βJ·U^T_{uvxy}/⟨σ_xσ_y⟩`, and the tight `lebowitz_four_zero_field` gives
`U^T_{uvxy} ≤ ⟨σ_uσ_x⟩⟨σ_vσ_y⟩+⟨σ_uσ_y⟩⟨σ_vσ_x⟩`; on a **degenerate** edge
`Current.doubledSourcefree_edgeExcess_reachable_eq` keeps the `weightSum` form
`2βJ(Z_{{u,v}△{x,y}}/Z_{x,y}−Z_{u,v}/Z_∅)` and the subtracted `Z_{u,v}/Z_∅≥0`
(GKS-I / `Current.weightSum_nonneg`) is dropped.

**Scope.**  This is the outer shell (M1) reducing `hLogLip` to the OZ convolution
ratio; it does **not** close `hLogLip` on its own — the `≤ K·d(x,y)` bound on the
right-hand side is gated on M2 (the sharp matching two-point lower bound, FFS
Ch. 12).  It discharges the crude-Lebowitz blow-up misdiagnosis.  (Glimm–Jaffe
Theorem 17.5.1, p. 312; issue #4386.) -/
theorem Current.log_correlation_beta_deriv_le_convolution (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] {x y : ↑Λ} (hxy : x ≠ y)
    (J : ℝ) {β : ℝ} (hβ : 0 < β) (hJ : 0 ≤ J)
    (hpos : 0 < correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}) :
    deriv (fun β' => Real.log
        (correlation (inducedGraph G Λ) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, y})) β
      ≤ ∑ e : (inducedGraph G Λ).edgeSet, Current.lebowitzEdgeBound G Λ J β x y e := by
  classical
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  rw [(Current.hasDerivAt_log_correlation_beta G Λ hxy J hβ hJ hpos).deriv,
    Current.doubledSourcefree_excess_eq_sum_edge G Λ x y hβ.le hJ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  -- Extract representatives `u, v` of the edge `e` and their distinctness.
  obtain ⟨u, v, hab⟩ : ∃ u v, (e : Sym2 ↑Λ) = s(u, v) :=
    Sym2.inductionOn (e : Sym2 ↑Λ) (fun u v => ⟨u, v, rfl⟩)
  have hadj : (inducedGraph G Λ).Adj u v := by
    have he := e.2
    rw [hab, SimpleGraph.mem_edgeSet] at he
    exact he
  have huv : u ≠ v := (inducedGraph G Λ).ne_of_adj hadj
  simp only [Current.lebowitzEdgeBound, hab, Sym2.lift_mk, Current.lebowitzEdgeBoundFun]
  split_ifs with hdisj
  · -- Non-degenerate edge: P1 truncated four-point + tight Lebowitz.
    have hu : u ∉ ({x, y} : Finset ↑Λ) := Finset.disjoint_left.mp hdisj (by simp)
    have hv : v ∉ ({x, y} : Finset ↑Λ) := Finset.disjoint_left.mp hdisj (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
    obtain ⟨hux, huy⟩ := hu
    obtain ⟨hvx, hvy⟩ := hv
    have hleb := Lebowitz.lebowitz_four_zero_field (inducedGraph G Λ) J β
      ⟨hJ, le_refl 0, hβ⟩ u v x y huv hux huy hvx hvy hxy
    rw [Current.doubledSourcefree_edgeExcess_eq_truncated4pt G Λ hβJ e u v x y
      huv hxy hab hdisj hpos.ne']
    set cxy := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} with hcxy
    set cuvxy := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v, x, y}
    set cuv := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, v}
    set cux := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, x}
    set cvy := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {v, y}
    set cuy := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {u, y}
    set cvx := correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {v, x}
    have hL : 1 / (2 * β) * (2 * (β * J) * (cuvxy - cuv * cxy) / cxy)
        = J * (cuvxy - cuv * cxy) / cxy := by
      field_simp
    rw [hL, div_le_div_iff₀ hpos hpos]
    nlinarith [mul_nonneg (mul_nonneg hJ hpos.le)
      (by linarith [hleb] : (0 : ℝ) ≤ cuv * cxy + cux * cvy + cuy * cvx - cuvxy)]
  · -- Degenerate edge: keep the `weightSum` form, drop the nonneg subtracted term.
    rw [Current.doubledSourcefree_edgeExcess_reachable_eq G Λ hβJ e u v x y huv hxy hab,
      correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ (symmDiff ({u, v} : Finset ↑Λ) {x, y}),
      correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y}]
    have hz0 : 0 < Current.weightSum G Λ ∅ β J := Current.weightSum_empty_pos G Λ hβJ
    have hzxy : 0 < Current.weightSum G Λ {x, y} β J := by
      have h1 : correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
          * Current.weightSum G Λ ∅ β J = Current.weightSum G Λ {x, y} β J := by
        rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ {x, y},
          div_mul_cancel₀ _ hz0.ne']
      rw [← h1]; exact mul_pos hpos hz0
    have hdiff : J * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
            / Current.weightSum G Λ ∅ β J)
          / (Current.weightSum G Λ {x, y} β J / Current.weightSum G Λ ∅ β J)
        - 1 / (2 * β) * (2 * (β * J)
            * (Current.weightSum G Λ (symmDiff ({u, v} : Finset ↑Λ) {x, y}) β J
                / Current.weightSum G Λ {x, y} β J
              - Current.weightSum G Λ {u, v} β J / Current.weightSum G Λ ∅ β J))
        = J * Current.weightSum G Λ {u, v} β J / Current.weightSum G Λ ∅ β J := by
      field_simp
      ring
    have hnn : 0 ≤ J * Current.weightSum G Λ {u, v} β J / Current.weightSum G Λ ∅ β J :=
      div_nonneg (mul_nonneg hJ (Current.weightSum_nonneg G Λ {u, v} hβJ)) hz0.le
    linarith [hdiff, hnn]

end Ambient

end IsingModel
