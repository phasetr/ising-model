import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallBoundaryInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd
import IsingModel.Concrete.LatticeSphereCard
import IsingModel.TranslationInvariance.Truncated
import IsingModel.LatticeExpSum

/-!
# Theorem eta-le-1 split — Phases 5-7 contraction factor and iterated contraction bound

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 5: Contraction factor -/

/-- **Contraction factor for radius `r`**: the weighted sum over boundary edges of the
sum of two-point correlations from the origin to each endpoint.

`contractionFactor d Λ p r := p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,`
`  Sym2.lift ⟨fun k l => corr∞{0, k} + corr∞{0, l}, ...⟩ e`

Under translation invariance (at `h = 0`), `corr∞{l, x} = corr∞{0, x - l}`, so the
ball-boundary inequality with `sup_{|x| ≥ n} corr∞{0, x}` bounded by
`contractionFactor * sup_{|y| ≥ n - r - 1} corr∞{0, y}` (see `shellSup_contraction`).

Key property: under `HasPolynomialDecay`, `contractionFactor d Λ p r → 0` as `r → ∞`,
so in particular `contractionFactor < 1` for large enough `r`. -/
noncomputable def contractionFactor (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (r : ℕ) : ℝ :=
  p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
    Sym2.lift ⟨fun k l =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
        + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
    fun k l => by ring⟩ e

/-- **Cardinality bound for the contraction factor**: each boundary-edge summand
`⟨σ_0σ_k⟩^∞ + ⟨σ_0σ_l⟩^∞` is at most `2` (correlations are `≤ 1`), so
`contractionFactor d Λ p r ≤ βJ · 2 · |latticeBallBoundaryEdges d r|`.

Together with `latticeBallBoundaryEdges_card_le` this bounds the contraction
factor by `βJ` times (twice) the cube edge count, the estimate used to make the
contraction factor `< 1` in a strong high-temperature regime (Issue #2931,
Phase 3a). -/
theorem contractionFactor_le_card (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((latticeBallBoundaryEdges d r).card : ℝ)) := by
  unfold contractionFactor
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  refine mul_le_mul_of_nonneg_left ?_ hβJ
  calc ∑ e ∈ latticeBallBoundaryEdges d r,
        Sym2.lift ⟨fun k l =>
          correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
        fun k l => by ring⟩ e
      ≤ ∑ _e ∈ latticeBallBoundaryEdges d r, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
        simp only [Sym2.lift_mk]
        have hk := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), k}
        have hl := correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), l}
        linarith
    _ = 2 * ((latticeBallBoundaryEdges d r).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Explicit high-temperature bound for the contraction factor**: chaining the
boundary-edge cardinality bound `latticeBallBoundaryEdges_card_le`, the induced
cube edge count `inducedLatticeGraph_card_edgeFinset_le`, and the cube cardinality
`card_cubicBox`, the contraction factor is bounded by
`βJ · 2 · (d · (2(r+1)+1)^d)`.

This makes the contraction factor explicitly controlled by `βJ` times a fixed
(volume-independent) combinatorial constant depending only on `d` and `r`, the
input for an unconditional strong-high-temperature `contractionFactor < 1`
(Issue #2931, Phase 3a). -/
theorem contractionFactor_le_high_temp_const (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) := by
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  have hcard : ((latticeBallBoundaryEdges d r).card : ℝ)
      ≤ ((inducedGraph (IsingModel.latticeGraph d)
          (cubicBox d (r + 1))).edgeFinset.card : ℝ) := by
    exact_mod_cast latticeBallBoundaryEdges_card_le d r
  have hedge := inducedLatticeGraph_card_edgeFinset_le d (cubicBox d (r + 1))
  have hbox : Fintype.card (↑(cubicBox d (r + 1)) : Type _)
      = (2 * (r + 1) + 1) ^ d := by
    rw [Fintype.card_coe]; exact card_cubicBox d (r + 1)
  rw [hbox] at hedge
  calc contractionFactor d Λ p r
      ≤ p.β * p.J * (2 * ((latticeBallBoundaryEdges d r).card : ℝ)) :=
        contractionFactor_le_card d Λ p hf r
    _ ≤ p.β * p.J *
          (2 * ((inducedGraph (IsingModel.latticeGraph d)
            (cubicBox d (r + 1))).edgeFinset.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hβJ
        exact mul_le_mul_of_nonneg_left hcard (by norm_num)
    _ ≤ p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hβJ
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact_mod_cast hedge

/-- **Unconditional strong-high-temperature contraction**: if `βJ` is small
enough that `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, then `contractionFactor d Λ p r < 1`
outright — no polynomial-decay hypothesis needed.

This discharges the `contractionFactor < 1` hypothesis of the spatial-decay /
susceptibility layer in an explicit (volume-independent) strong-high-temperature
regime, via `contractionFactor_le_high_temp_const`.  Part of Issue #2931,
Phase 3a. -/
theorem contractionFactor_lt_one_of_high_temp (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    contractionFactor d Λ p r < 1 :=
  lt_of_le_of_lt (contractionFactor_le_high_temp_const d Λ p hf r) hht

/-- **The contraction factor is non-negative**: `0 ≤ contractionFactor d Λ p r`.

Follows from `p.β * p.J ≥ 0` (ferromagnetic) and
`correlationInfinite ≥ 0` (ferromagnetic). -/
theorem contractionFactor_nonneg (d : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : ℕ) :
    0 ≤ contractionFactor d Λ p r := by
  unfold contractionFactor
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg
  intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
  · exact correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _

/-- **Surface bound on the boundary-edge count**: every ball-boundary edge has
its inside endpoint (the one at distance exactly `r`) on the ℓ¹-sphere, and each
sphere vertex is incident to at most `2d` lattice edges, so
`|latticeBallBoundaryEdges d r| ≤ 2d · |latticeSphere d r|`. Together with
`latticeSphere_card_le'` this gives the `O(r^{d-1})` *surface* growth that the
crude `O(r^d)` volume bound (`latticeBallBoundaryEdges_card_le`) misses. -/
theorem latticeBallBoundaryEdges_card_le_sphere (d r : ℕ) :
    (latticeBallBoundaryEdges d r).card ≤ 2 * d * (latticeSphere d r).card := by
  classical
  have hsub : latticeBallBoundaryEdges d r ⊆
      (latticeSphere d r).biUnion
        (fun v => (latticeBallBoundaryEdges d r).filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
    obtain ⟨hadj, hstr⟩ := mem_latticeBallBoundaryEdges.mp he
    have hkl1 : IsingModel.latticeDistance d k l = 1 :=
      (latticeGraph_adj_iff_latticeDistance_eq_one d k l).mp hadj
    have hlk1 : IsingModel.latticeDistance d l k = 1 :=
      (latticeGraph_adj_iff_latticeDistance_eq_one d l k).mp hadj.symm
    have htri_l := IsingModel.latticeDistance_triangle d 0 k l
    have htri_k := IsingModel.latticeDistance_triangle d 0 l k
    rw [Finset.mem_biUnion]
    by_cases hk : IsingModel.latticeDistance d 0 k ≤ r
    · have hdl : ¬ IsingModel.latticeDistance d 0 l ≤ r := fun h =>
        hstr (propext ⟨fun _ => h, fun _ => hk⟩)
      exact ⟨k, mem_latticeSphere.mpr (by omega),
        Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_left k l⟩⟩
    · have hl : IsingModel.latticeDistance d 0 l ≤ r := by
        by_contra hl; exact hstr (propext ⟨fun h => absurd h hk, fun h => absurd h hl⟩)
      exact ⟨l, mem_latticeSphere.mpr (by omega),
        Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_right k l⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ (2 * d) ?_) (le_of_eq (Nat.mul_comm _ _))
  intro v _
  -- boundary edges are lattice edges
  have hbd_edge : ∀ {e : Sym2 (Fin d → ℤ)}, e ∈ latticeBallBoundaryEdges d r →
      e ∈ (IsingModel.latticeGraph d).edgeSet := by
    intro e he
    obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
    exact (SimpleGraph.mem_edgeSet (IsingModel.latticeGraph d)).mpr
      (mem_latticeBallBoundaryEdges.mp he).1
  -- each sphere vertex is on ≤ 2d boundary edges (inject by the other endpoint)
  refine le_trans (Finset.card_le_card_of_injOn
    (s := (latticeBallBoundaryEdges d r).filter (fun e => v ∈ e))
    (t := (IsingModel.latticeGraph d).neighborFinset v)
    (fun e => if h : v ∈ e then Sym2.Mem.other h else v) ?_ ?_) ?_
  · intro e he'
    rw [Finset.coe_filter, Set.mem_setOf_eq] at he'
    obtain ⟨heB, hve⟩ := he'
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset, dif_pos hve]
    exact (SimpleGraph.mem_edgeSet (IsingModel.latticeGraph d)).mp
      ((Sym2.other_spec hve).symm ▸ hbd_edge heB)
  · intro e₁ he₁ e₂ he₂ hf12
    rw [Finset.coe_filter, Set.mem_setOf_eq] at he₁ he₂
    simp only [dif_pos he₁.2, dif_pos he₂.2] at hf12
    rw [← Sym2.other_spec he₁.2, ← Sym2.other_spec he₂.2, hf12]
  · rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact latticeGraph_degree_le d v

set_option maxHeartbeats 1600000 in
-- The proof combines a polynomial-decay extraction (cofinite → bounded distance),
-- a per-edge bound, a surface cardinality estimate, and a real arithmetic chain;
-- the combined elaboration exceeds the default heartbeat limit.
/-- **Polynomial decay implies the contraction factor tends to zero**
(GJ §17.8, p. 317; formerly an axiom): under `HasPolynomialDecay d Λ p`,
`contractionFactor d Λ p r → 0` as `r → ∞`.

The boundary `latticeBallBoundaryEdges d r` has only `O(r^{d-1})` edges
(`latticeBallBoundaryEdges_card_le_sphere` + `latticeSphere_card_le'`), and each
endpoint sits at distance in `{r, r+1}`, where polynomial decay forces
`corr∞{0, ·}·dist^{d-1} ≤ δ`. The volume-cancelling product
`O(r^{d-1}) · O(r^{-(d-1)})·δ ≤ C·δ` is made small by choosing `δ` small.

Reference: Glimm–Jaffe §17.8 pp. 316–318. -/
theorem polynomialDecay_contraction_factor_tendsto (d : ℕ) (hd : 1 ≤ d)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (_hh : p.h = 0)
    (hpoly : HasPolynomialDecay d Λ p) :
    Filter.Tendsto (contractionFactor d Λ p) Filter.atTop (nhds 0) := by
  classical
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the configuration-independent constant and the polynomial-decay threshold
  set C : ℝ := p.β * p.J * (8 * (d : ℝ) * 3 ^ (d - 1)) + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  set δ : ℝ := ε / C with hδ
  have hδpos : 0 < δ := div_pos hε hCpos
  -- Polynomial-decay extraction: the bad set `{ δ ≤ corr·dist^{d-1} }` is finite.
  have hcofin : {x : {x : Fin d → ℤ // x ≠ 0} |
      δ ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), x.val}
        * (IsingModel.latticeDistance d 0 x.val : ℝ) ^ (d - 1)}.Finite := by
    have h1 := (Metric.tendsto_nhds.mp hpoly) δ hδpos
    rw [Filter.eventually_cofinite] at h1
    refine h1.subset (fun x hx => ?_)
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg (correlationInfinite_nonneg _ _ _ hf _) (by positivity))]
    linarith
  -- the bad set has bounded distance to the origin
  obtain ⟨D, hD⟩ :=
    (hcofin.image (fun x => IsingModel.latticeDistance d 0 x.val)).bddAbove
  -- per-vertex decay bound beyond distance `D`
  have hpv : ∀ v : Fin d → ℤ, D < IsingModel.latticeDistance d 0 v →
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), v}
        * (IsingModel.latticeDistance d 0 v : ℝ) ^ (d - 1) ≤ δ := by
    intro v hvD
    have hv0 : v ≠ 0 := by
      intro h; rw [h, IsingModel.latticeDistance_self] at hvD; omega
    by_contra hcon
    rw [not_le] at hcon
    have hmem : (⟨v, hv0⟩ : {x : Fin d → ℤ // x ≠ 0}) ∈ {x : {x : Fin d → ℤ // x ≠ 0} |
        δ ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), x.val}
          * (IsingModel.latticeDistance d 0 x.val : ℝ) ^ (d - 1)} := le_of_lt hcon
    have : IsingModel.latticeDistance d 0 v ≤ D :=
      hD (Set.mem_image_of_mem _ hmem)
    omega
  refine ⟨D + 1, fun r hrN => ?_⟩
  have hr1 : 1 ≤ r := by omega
  have hrp_pos : (0 : ℝ) < (r : ℝ) ^ (d - 1) := by positivity
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (contractionFactor_nonneg d Λ p hf r)]
  -- per-edge bound: every boundary-edge summand is `≤ 2δ / r^{d-1}`
  have hedge : ∀ e ∈ latticeBallBoundaryEdges d r,
      Sym2.lift ⟨fun k l =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
          + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
        fun k l => by ring⟩ e ≤ 2 * δ / (r : ℝ) ^ (d - 1) := by
    intro e he
    obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    obtain ⟨hadj, hstr⟩ := mem_latticeBallBoundaryEdges.mp he
    have hkl1 : IsingModel.latticeDistance d k l = 1 :=
      (latticeGraph_adj_iff_latticeDistance_eq_one d k l).mp hadj
    have hlk1 : IsingModel.latticeDistance d l k = 1 :=
      (latticeGraph_adj_iff_latticeDistance_eq_one d l k).mp hadj.symm
    have htri_l := IsingModel.latticeDistance_triangle d 0 k l
    have htri_k := IsingModel.latticeDistance_triangle d 0 l k
    have hge : r ≤ IsingModel.latticeDistance d 0 k ∧ r ≤ IsingModel.latticeDistance d 0 l := by
      by_cases hk : IsingModel.latticeDistance d 0 k ≤ r
      · have hdl : ¬ IsingModel.latticeDistance d 0 l ≤ r := fun h =>
          hstr (propext ⟨fun _ => h, fun _ => hk⟩)
        exact ⟨by omega, by omega⟩
      · have hl : IsingModel.latticeDistance d 0 l ≤ r := by
          by_contra hl; exact hstr (propext ⟨fun h => absurd h hk, fun h => absurd h hl⟩)
        exact ⟨by omega, by omega⟩
    -- each endpoint correlation, scaled by `r^{d-1}`, is `≤ δ`
    have hbound : ∀ {v : Fin d → ℤ}, r ≤ IsingModel.latticeDistance d 0 v →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), v}
          * (r : ℝ) ^ (d - 1) ≤ δ := by
      intro v hv
      have hvD : D < IsingModel.latticeDistance d 0 v := by omega
      have hmono : (r : ℝ) ^ (d - 1) ≤ (IsingModel.latticeDistance d 0 v : ℝ) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hv) _
      exact le_trans (mul_le_mul_of_nonneg_left hmono
        (correlationInfinite_nonneg _ _ _ hf _)) (hpv v hvD)
    rw [le_div_iff₀ hrp_pos]
    nlinarith [hbound hge.1, hbound hge.2]
  -- assemble: sum over the `O(r^{d-1})` boundary edges
  have hEd : ((latticeBallBoundaryEdges d r).card : ℝ)
      ≤ 4 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ (d - 1) := by
    have h1 := latticeBallBoundaryEdges_card_le_sphere d r
    have h2 := latticeSphere_card_le' d r hd
    have h3 : (latticeBallBoundaryEdges d r).card ≤ 2 * d * (2 * (2 * r + 1) ^ (d - 1)) :=
      le_trans h1 (Nat.mul_le_mul le_rfl h2)
    calc ((latticeBallBoundaryEdges d r).card : ℝ)
        ≤ ((2 * d * (2 * (2 * r + 1) ^ (d - 1)) : ℕ) : ℝ) := by exact_mod_cast h3
      _ = 4 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ (d - 1) := by push_cast; ring
  have hpow : (2 * (r : ℝ) + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * (r : ℝ) ^ (d - 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have hfrac : (2 * (r : ℝ) + 1) ^ (d - 1) / (r : ℝ) ^ (d - 1) ≤ 3 ^ (d - 1) := by
    rw [div_le_iff₀ hrp_pos]; exact hpow
  -- final real chain
  have hsum_nonneg : 0 ≤ 2 * δ / (r : ℝ) ^ (d - 1) := by positivity
  have h8dδ_nn : (0 : ℝ) ≤ 8 * (d : ℝ) * δ := by positivity
  calc contractionFactor d Λ p r
      = p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
            fun k l => by ring⟩ e := by rw [contractionFactor]
    _ ≤ p.β * p.J * ∑ _e ∈ latticeBallBoundaryEdges d r, 2 * δ / (r : ℝ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hedge) hβJ
    _ = p.β * p.J * (((latticeBallBoundaryEdges d r).card : ℝ) * (2 * δ / (r : ℝ) ^ (d - 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ p.β * p.J * ((4 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ (d - 1)) * (2 * δ / (r : ℝ) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEd hsum_nonneg) hβJ
    _ = p.β * p.J * (8 * (d : ℝ) * δ * ((2 * (r : ℝ) + 1) ^ (d - 1) / (r : ℝ) ^ (d - 1))) := by
        ring
    _ ≤ p.β * p.J * (8 * (d : ℝ) * δ * 3 ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfrac h8dδ_nn) hβJ
    _ = p.β * p.J * (8 * (d : ℝ) * 3 ^ (d - 1)) * δ := by ring
    _ < ε := by
        rw [hδ, ← mul_div_assoc, div_lt_iff₀ hCpos, hC]
        nlinarith [hε, hβJ, (by positivity : (0:ℝ) ≤ 8 * (d:ℝ) * 3 ^ (d-1))]

/-! ## Phase 6: Shell-supremum contraction -/

/-- **Nonemptiness of a distance shell**: for `1 ≤ d` and `1 ≤ m` the shell
`{y : Fin d → ℤ // m ≤ latticeDistance d 0 y ∧ y ≠ 0}` is nonempty (the point with
first coordinate `m`). -/
private theorem shell_nonempty {d : ℕ} (hd : 1 ≤ d) {m : ℕ} (hm : 1 ≤ m) :
    Nonempty {y : Fin d → ℤ // m ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} := by
  let y₀ : Fin d → ℤ := fun i => if i = (⟨0, by omega⟩ : Fin d) then (m : ℤ) else 0
  refine ⟨⟨y₀, ?_, ?_⟩⟩
  · unfold IsingModel.latticeDistance y₀
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
    let f : Fin d → ℕ := fun i => (if i = (⟨0, by omega⟩ : Fin d) then (m : ℤ) else 0).natAbs
    have hle : f (⟨0, by omega⟩ : Fin d) ≤ ∑ i : Fin d, f i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
    have hf0 : f (⟨0, by omega⟩ : Fin d) = m := by
      simp [f]
    calc m = f (⟨0, by omega⟩ : Fin d) := hf0.symm
      _ ≤ ∑ i : Fin d, f i := hle
  · intro h
    have := congrFun h (⟨0, by omega⟩ : Fin d)
    simp only [y₀, if_pos rfl, Pi.zero_apply] at this
    omega

/-- **Boundary-edge endpoints are within distance `r + 1`**: every endpoint of a
ball-boundary edge has `latticeDistance d 0 · ≤ r + 1` (the inside endpoint is at
distance `≤ r`, the outside one at exactly `r + 1`). -/
theorem latticeBallBoundaryEdges_dist_le {d r : ℕ} {k l : Fin d → ℤ}
    (h : s(k, l) ∈ latticeBallBoundaryEdges d r) :
    IsingModel.latticeDistance d 0 k ≤ r + 1 ∧ IsingModel.latticeDistance d 0 l ≤ r + 1 := by
  obtain ⟨hadj, hstr⟩ := mem_latticeBallBoundaryEdges.mp h
  have hlk : IsingModel.latticeDistance d l k = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d l k).mp hadj.symm
  have hkl : IsingModel.latticeDistance d k l = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d k l).mp hadj
  have h1 := IsingModel.latticeDistance_triangle d 0 l k
  have h2 := IsingModel.latticeDistance_triangle d 0 k l
  by_cases hA : IsingModel.latticeDistance d 0 k ≤ r
  · exact ⟨by omega, by omega⟩
  · have hB : IsingModel.latticeDistance d 0 l ≤ r := by
      by_contra hB
      exact hstr (propext ⟨fun h => absurd h hA, fun h => absurd h hB⟩)
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 1600000 in
-- The proof per shell point applies the ball-boundary inequality, translation
-- invariance, and a triangle-inequality shell bound, then aggregates over the
-- boundary-edge sum; the combined elaboration exceeds the default heartbeat limit.
/-- **Shell supremum contraction** (key inductive step of GJ §17.8, p. 317;
formerly an axiom): for `1 ≤ r` and `n > r + 1`,

`⨆ {|y| ≥ n} corr∞{0, y} ≤ contractionFactor d Λ p r * ⨆ {|y| ≥ n - r - 1} corr∞{0, y}`.

For each `y` with `|y| ≥ n`, `ball_boundary_tight_infinite` gives
`corr∞{0,y} ≤ βJ·∑_{(k,l)∈∂B_r}[corr∞{0,k}·corr∞{l,y} + corr∞{0,l}·corr∞{k,y}]`;
translation invariance turns `corr∞{l,y}` into `corr∞{0,y−l}` with
`|y−l| ≥ |y| − (r+1) ≥ n − r − 1` (boundary endpoints have distance `≤ r+1`), so
each `corr∞{l,y}, corr∞{k,y}` is `≤` the `(n−r−1)`-shell supremum `S`, whence
`corr∞{0,y} ≤ (βJ·∑(corr∞{0,k}+corr∞{0,l}))·S = contractionFactor · S`.

The hypothesis `1 ≤ r` (new relative to the former axiom) is required because
`ball_boundary_tight_infinite` is false at `r = 0`. -/
theorem shellSup_contraction (d : ℕ) (hd : 1 ≤ d)
    (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (n : ℕ) (hn : r + 1 < n) :
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ contractionFactor d Λ p r *
        ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} := by
  classical
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  -- The (n-r-1)-shell supremum `S`.
  set S := ⨆ (z : {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0}),
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), z.val} with hSdef
  have hSbdd : BddAbove (Set.range
      (fun z : {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), z.val})) := by
    refine ⟨1, ?_⟩
    rintro x ⟨z, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  -- `S ≥ 0`.
  haveI hSne : Nonempty {z : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} :=
    shell_nonempty hd (by omega)
  have hSnonneg : 0 ≤ S := by
    rw [hSdef]
    exact le_ciSup_of_le hSbdd (Classical.arbitrary _)
      (correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
  haveI hLne : Nonempty {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} :=
    shell_nonempty hd (by omega)
  apply ciSup_le
  rintro ⟨y, hyn, hy0⟩
  -- Per shell point `y`: apply the ball-boundary inequality.
  have hx : r + 1 < IsingModel.latticeDistance d 0 y := by omega
  have hbb := ball_boundary_tight_infinite d hd r hr Λ p hf hh y hx
  -- Bound each boundary endpoint's far correlation by `S`.
  have hfar : ∀ {w : Fin d → ℤ}, IsingModel.latticeDistance d 0 w ≤ r + 1 →
      correlationInfinite (IsingModel.latticeGraph d) Λ p {w, y} ≤ S := by
    intro w hw
    -- corr∞{w, y} = corr∞{0, y - w} by translation invariance.
    have hvadd : correlationInfinite (IsingModel.latticeGraph d) Λ p
        (vaddFinset (-w) ({w, y} : Finset (Fin d → ℤ)))
        = correlationInfinite (IsingModel.latticeGraph d) Λ p ({w, y} : Finset (Fin d → ℤ)) :=
      correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant d Λ (-w) p hf {w, y}
    rw [vaddFinset_pair] at hvadd
    simp only [vadd_eq_add, neg_add_cancel, neg_add_eq_sub] at hvadd
    -- hvadd : corr∞{0, y - w} = corr∞{w, y}
    rw [← hvadd]
    -- distance of `y - w` to the origin.
    have hd_eq : IsingModel.latticeDistance d 0 (y - w) = IsingModel.latticeDistance d w y := by
      unfold IsingModel.latticeDistance
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, Int.natAbs_neg]
      rw [show w i - y i = -(y i - w i) from by ring, Int.natAbs_neg]
    have htri := IsingModel.latticeDistance_triangle d 0 w y
    have hdist_yw : n - r - 1 ≤ IsingModel.latticeDistance d 0 (y - w) := by
      rw [hd_eq]; omega
    have hne_yw : y - w ≠ 0 := by
      intro h
      rw [h] at hdist_yw
      simp only [IsingModel.latticeDistance_self] at hdist_yw
      omega
    rw [hSdef]
    exact le_ciSup_of_le hSbdd ⟨y - w, hdist_yw, hne_yw⟩ le_rfl
  -- Aggregate over the boundary-edge sum.
  refine le_trans hbb ?_
  have hsum : (∑ e ∈ latticeBallBoundaryEdges d r,
      Sym2.lift ⟨fun k l =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y}
        + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y},
      fun k l => by ring⟩ e)
      ≤ (∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
          fun k l => by ring⟩ e) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun e he => ?_)
    obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    obtain ⟨hdk, hdl⟩ := latticeBallBoundaryEdges_dist_le he
    have hly : correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y} ≤ S := hfar hdl
    have hky : correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y} ≤ S := hfar hdk
    have h0k : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    have h0l : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l} :=
      correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
    nlinarith [mul_le_mul_of_nonneg_left hly h0k, mul_le_mul_of_nonneg_left hky h0l]
  calc p.β * p.J * (∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, y}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, y},
          fun k l => by ring⟩ e)
      ≤ p.β * p.J * ((∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l},
          fun k l => by ring⟩ e) * S) := mul_le_mul_of_nonneg_left hsum hβJ
    _ = contractionFactor d Λ p r * S := by rw [contractionFactor]; ring

/-! ## Phase 7: Iterated contraction bound (axiom) -/

/-- **Shell supremum iterated bound** (axiom, iterated application of `shellSup_contraction`):

Fix `r : ℕ` and `α = contractionFactor d Λ p r` with `α < 1`. Set step size `s = r + 2`.
For all `k : ℕ` and all `n ≥ k * s`:

  `⨆ {|y| ≥ n} corr∞{0, y} ≤ α^k`

**Proof sketch (deferred)**: By induction on `k`.
- Base `k = 0`: the sup is `≤ 1 = α^0` from `correlationInfinite_le_one`.
- Step: for `n ≥ (k+1) * s = k * s + r + 2 > r + 1`,
  apply `shellSup_contraction` at `n` to get
  `sup(n) ≤ α * sup(n - r - 1)`.
  Since `n - r - 1 ≥ k * s`, the inductive hypothesis gives `sup(n - r - 1) ≤ α^k`.
  Thus `sup(n) ≤ α * α^k = α^(k+1)`.

Reference: Glimm–Jaffe §17.8 proof of Thm 17.8.1, p. 317. -/
theorem shellSup_iterated_bound (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (_hα : contractionFactor d Λ p r < 1)
    (k : ℕ) : ∀ n : ℕ, k * (r + 2) ≤ n →
    ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
        correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
      ≤ (contractionFactor d Λ p r) ^ k := by
  induction k with
  | zero =>
    intro n _
    simp only [pow_zero]
    -- For any n and d ≥ 1, the index type is nonempty:
    -- take y = (n+1, 0, ..., 0), which has latticeDistance = n+1 ≥ n and y ≠ 0.
    haveI hnem : Nonempty {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0} := by
      let y₀ : Fin d → ℤ := fun i => if i = ⟨0, by omega⟩ then (n : ℤ) + 1 else 0
      refine ⟨⟨y₀, ?_, ?_⟩⟩
      · -- n ≤ latticeDistance d 0 y₀
        unfold IsingModel.latticeDistance y₀
        simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
        let f : Fin d → ℕ := fun i =>
          (if i = (⟨0, by omega⟩ : Fin d) then (n : ℤ) + 1 else 0).natAbs
        have hle : f (⟨0, by omega⟩ : Fin d) ≤ ∑ i : Fin d, f i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        have hf0 : f (⟨0, by omega⟩ : Fin d) = n + 1 := by
          simp only [f, ite_true]; norm_cast
        calc n ≤ n + 1 := Nat.le_succ n
          _ = f (⟨0, by omega⟩ : Fin d) := hf0.symm
          _ ≤ ∑ i : Fin d, f i := hle
      · -- y₀ ≠ 0
        intro h
        have := congrFun h (⟨0, by omega⟩ : Fin d)
        simp only [y₀, ite_true, Pi.zero_apply] at this
        omega
    apply ciSup_le
    rintro ⟨y, -, -⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  | succ k ih =>
    intro n hn
    -- n ≥ (k+1)*(r+2) ≥ r+2 > r+1
    have hn_gt : r + 1 < n := by
      have h1 : (k + 1) * (r + 2) ≥ r + 2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
      omega
    -- Apply shellSup_contraction
    have hstep : k * (r + 2) ≤ n - r - 1 := by
      have h1 : (k + 1) * (r + 2) = k * (r + 2) + (r + 2) := by ring
      omega
    calc ⨆ (y : {y : Fin d → ℤ // n ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val}
        ≤ contractionFactor d Λ p r *
          ⨆ (y : {y : Fin d → ℤ // (n - r - 1) ≤ IsingModel.latticeDistance d 0 y ∧ y ≠ 0}),
              correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y.val} :=
              shellSup_contraction d hd r hr Λ p hf hh n hn_gt
      _ ≤ contractionFactor d Λ p r * (contractionFactor d Λ p r) ^ k :=
          mul_le_mul_of_nonneg_left (ih (n - r - 1) hstep) (contractionFactor_nonneg d Λ p hf r)
      _ = (contractionFactor d Λ p r) ^ (k + 1) := by rw [pow_succ]; ring

/-- **Pointwise spatial exponential decay of the infinite-volume correlation**:
the shell-iterated bound specializes to a per-point estimate
`⟨σ_0σ_y⟩^∞ ≤ (contractionFactor d Λ p r)^{dist(0,y) / (r+2)}` for every `y ≠ 0`,
where the exponent is the natural-number division `dist(0,y) / (r+2)`.

Since `(dist(0,y) / (r+2)) · (r+2) ≤ dist(0,y)`, the point `y` lies in the
distance-`dist(0,y)` shell, so its correlation is bounded by the shell supremum,
which `shellSup_iterated_bound` controls by `(contractionFactor)^{dist/(r+2)}`.
This is the prefactor-free spatial exponential decay in the form used by the
finite-volume convergence-rate program (Issue #2931, Phase 3a/3b′). -/
theorem correlationInfinite_latticeGraph_le_contractionFactor_pow_dist
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) {y : Fin d → ℤ} (hy : y ≠ 0) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
      ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d 0 y / (r + 2)) := by
  set k := IsingModel.latticeDistance d 0 y / (r + 2) with hk
  have hkr : k * (r + 2) ≤ IsingModel.latticeDistance d 0 y := Nat.div_mul_le_self _ _
  have hbound :=
    shellSup_iterated_bound d hd r hr Λ p hf hh hα k (IsingModel.latticeDistance d 0 y) hkr
  have hbdd :
      BddAbove (Set.range (fun z : {z : Fin d → ℤ //
          IsingModel.latticeDistance d 0 y ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0} =>
        correlationInfinite (IsingModel.latticeGraph d) Λ p
          {(0 : Fin d → ℤ), z.val})) := by
    refine ⟨1, ?_⟩
    rintro x ⟨z, rfl⟩
    exact correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
  have hle :
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
        ≤ ⨆ (z : {z : Fin d → ℤ //
            IsingModel.latticeDistance d 0 y ≤ IsingModel.latticeDistance d 0 z ∧ z ≠ 0}),
          correlationInfinite (IsingModel.latticeGraph d) Λ p
            {(0 : Fin d → ℤ), z.val} :=
    le_ciSup hbdd ⟨y, le_rfl, hy⟩
  exact hle.trans hbound

/-- **Pointwise spatial exponential decay for an arbitrary pair**: translation
invariance extends the anchored bound to any distinct pair `i ≠ j`,
`⟨σ_iσ_j⟩^∞ ≤ (contractionFactor d Λ p r)^{dist(i,j) / (r+2)}`.

The correlation is translation invariant
(`correlationInfinite_vaddFinset_of_translationInvariant`), so
`⟨σ_iσ_j⟩^∞ = ⟨σ_0σ_{j-i}⟩^∞`, and the ℓ¹ lattice distance is likewise
translation invariant, `dist(i,j) = dist(0, j-i)`; the anchored bound
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist` then applies at
`y = j - i ≠ 0`.  This is the per-pair prefactor-free spatial decay used by the
finite-volume convergence-rate program (Issue #2931, Phase 3a/3b′). -/
theorem correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
      ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2)) := by
  -- Translation invariance: `⟨σ_iσ_j⟩^∞ = ⟨σ_0σ_{j-i}⟩^∞`.
  have htrans :
      correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        = correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), j - i} := by
    rw [show ({i, j} : Finset (Fin d → ℤ)) = vaddFinset i {(0 : Fin d → ℤ), j - i} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ i p hf {(0 : Fin d → ℤ), j - i}
  -- The ℓ¹ distance is translation invariant: `dist(i,j) = dist(0, j-i)`.
  have hdist : IsingModel.latticeDistance d i j
      = IsingModel.latticeDistance d 0 (j - i) := by
    unfold IsingModel.latticeDistance
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Pi.zero_apply, zero_sub, Pi.sub_apply]
    congr 1; ring
  -- `j - i ≠ 0` since `i ≠ j`.
  have hjmi_ne : j - i ≠ 0 := fun h => hij (by
    have hji : j = i + (j - i) := by abel
    rw [h, add_zero] at hji; exact hji.symm)
  rw [htrans, hdist]
  exact correlationInfinite_latticeGraph_le_contractionFactor_pow_dist
    d hd r hr Λ p hf hh hα hjmi_ne

/-- **Uniform clustering at large distance**: when the contraction factor is
`< 1`, the infinite-volume pair correlation is uniformly small at large lattice
distance — for every `ε > 0` there is `R` such that
`⟨σ_iσ_j⟩^∞ ≤ ε` for all pairs with `dist(i,j) ≥ R`.

Since `contractionFactor d Λ p r < 1`, some power `(contractionFactor)^m < ε`;
taking `R = (m+1)(r+2)` forces `dist(i,j)/(r+2) ≥ m`, so the per-pair spatial
decay bound `correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair`
gives `⟨σ_iσ_j⟩^∞ ≤ (contractionFactor)^{dist/(r+2)} ≤ (contractionFactor)^m < ε`.
This is the uniform clustering property of the infinite-volume measure
(Issue #2931, Phase 3a). -/
theorem correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) :
    ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ i j : Fin d → ℤ,
      R ≤ IsingModel.latticeDistance d i j →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} ≤ ε := by
  intro ε hε
  have hcf0 : 0 ≤ contractionFactor d Λ p r := contractionFactor_nonneg d Λ p hf r
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hα
  refine ⟨(m + 1) * (r + 2), fun i j hR => ?_⟩
  by_cases hij : i = j
  · exfalso
    rw [hij, IsingModel.latticeDistance_self] at hR
    have : 0 < (m + 1) * (r + 2) := Nat.mul_pos (Nat.succ_pos m) (by omega)
    omega
  · have hbound :=
      correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
        d hd r hr Λ p hf hh hα hij
    have hexp : m ≤ IsingModel.latticeDistance d i j / (r + 2) := by
      have hge : (m + 1) ≤ IsingModel.latticeDistance d i j / (r + 2) := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < r + 2)]
        exact hR
      omega
    have hmono :
        (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2))
          ≤ (contractionFactor d Λ p r) ^ m :=
      pow_le_pow_of_le_one hcf0 hα.le hexp
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        ≤ (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2)) := hbound
      _ ≤ (contractionFactor d Λ p r) ^ m := hmono
      _ ≤ ε := hm.le

/-- **The infinite-volume correlation kernel vanishes at infinity (cofinite)**:
when the contraction factor is `< 1`, `y ↦ ⟨σ_0σ_y⟩^∞` tends to `0` along the
cofinite filter on `ℤ^d`.

This is the `C₀`/clustering form of the uniform large-distance decay: for every
`ε > 0` the exceptional set `{y : ε ≤ ⟨σ_0σ_y⟩^∞}` is contained in the finite
lattice ball `{y : dist(0,y) ≤ R}` (by
`correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one` and
the finiteness of lattice balls `latticeDistance_le_finite`), hence finite, so
the values are eventually below `ε`.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_tendsto_cofinite_zero
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hα : contractionFactor d Λ p r < 1) :
    Filter.Tendsto
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y})
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ :=
    correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
      d hd r hr Λ p hf hh hα (ε / 2) (by linarith)
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (IsingModel.latticeDistance_le_finite d 0 R) ?_
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  by_contra hcontra
  have hge : R ≤ IsingModel.latticeDistance d 0 y := le_of_lt (not_le.mp hcontra)
  have hcorr_le := hR 0 y hge
  have hcorr_nn := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf
    {(0 : Fin d → ℤ), y}
  apply hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hcorr_nn]
  linarith

/-- **Finite susceptibility from the contraction factor**: when
`0 < contractionFactor d Λ p r < 1`, the infinite-volume correlation kernel
`y ↦ ⟨σ_0σ_y⟩^∞` is summable over `ℤ^d`, i.e. the magnetic susceptibility
`χ = ∑_y ⟨σ_0σ_y⟩^∞` is finite.

The per-pair spatial decay `⟨σ_0σ_y⟩^∞ ≤ (contractionFactor)^{dist(0,y)/(r+2)}`
is dominated by `(1/contractionFactor)·exp(-m·dist(0,y))` with
`m = -log(contractionFactor)/(r+2) > 0` (using
`(cf)^{⌊dist/(r+2)⌋} ≤ (cf)^{dist/(r+2)-1} = (1/cf)·exp(-m·dist)`), and the
exponential kernel is summable over the lattice by `summable_exp_neg_dist`; the
comparison test concludes.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hcf_pos : 0 < contractionFactor d Λ p r) (hα : contractionFactor d Λ p r < 1) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}) := by
  set cf := contractionFactor d Λ p r with hcfdef
  set m := -Real.log cf / (r + 2 : ℝ) with hmdef
  have hr2_pos : (0 : ℝ) < (r + 2 : ℝ) := by positivity
  have hlog_neg : Real.log cf < 0 := Real.log_neg hcf_pos hα
  have hm_pos : 0 < m := by
    rw [hmdef]; exact div_pos (by linarith [hlog_neg]) hr2_pos
  have hmaj_sum :
      Summable (fun y : Fin d → ℤ =>
        (1 / cf) * Real.exp (-m * (IsingModel.latticeDistance d 0 y : ℝ))) :=
    (summable_exp_neg_dist hm_pos d 0).mul_left (1 / cf)
  refine Summable.of_nonneg_of_le
    (fun y => correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
    (fun y => ?_) hmaj_sum
  by_cases hy : y = 0
  · -- `dist(0,0) = 0`: majorant is `1/cf ≥ 1 ≥ correlation`.
    subst hy
    have hone : correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), 0} ≤ 1 :=
      correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
    have hinv : (1 : ℝ) ≤ 1 / cf := by
      rw [le_div_iff₀ hcf_pos]; linarith
    have hdist0 : IsingModel.latticeDistance d 0 (0 : Fin d → ℤ) = 0 :=
      IsingModel.latticeDistance_self d 0
    rw [hdist0]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    linarith
  · have hbound :=
      correlationInfinite_latticeGraph_le_contractionFactor_pow_dist d hd r hr Λ p hf hh hα hy
    -- `cf^q ≤ (1/cf)·exp(-m·dist)` with `q = dist/(r+2)`.
    set n := IsingModel.latticeDistance d 0 y with hndef
    have hq_real : ((n / (r + 2) : ℕ) : ℝ) ≥ (n : ℝ) / (r + 2 : ℝ) - 1 := by
      have hlt : n < (n / (r + 2) + 1) * (r + 2) := by
        have hmod := Nat.mod_lt n (show 0 < r + 2 by omega)
        have hdm := Nat.div_add_mod n (r + 2)
        nlinarith [hmod, hdm]
      have hlt' : (n : ℝ) < ((n / (r + 2) : ℕ) : ℝ) * (r + 2 : ℝ) + (r + 2 : ℝ) := by
        have := (Nat.cast_lt (α := ℝ)).2 hlt
        push_cast at this ⊢; nlinarith [this]
      rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hr2_pos]
      nlinarith [hlt']
    have hcfle1 : cf ≤ 1 := hα.le
    -- `cf^(q:ℕ) = cf^(q:ℝ) ≤ cf^((n/(r+2)) - 1)` (base in (0,1], exponent larger).
    have hstep1 :
        cf ^ (n / (r + 2)) ≤ cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := by
      rw [← Real.rpow_natCast cf (n / (r + 2))]
      exact Real.rpow_le_rpow_of_exponent_ge hcf_pos hcfle1 hq_real
    have hstep2 :
        cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1)
          = (1 / cf) * Real.exp (-m * (n : ℝ)) := by
      rw [Real.rpow_sub hcf_pos, Real.rpow_one, Real.rpow_def_of_pos hcf_pos,
        one_div, div_eq_mul_inv, mul_comm (cf⁻¹) (Real.exp (-m * (n : ℝ)))]
      congr 1
      congr 1
      rw [hmdef]; ring
    calc correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}
        ≤ cf ^ (n / (r + 2)) := hbound
      _ ≤ cf ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := hstep1
      _ = (1 / cf) * Real.exp (-m * (n : ℝ)) := hstep2

/-- **Finite susceptibility from any basepoint**: by translation invariance, the
correlation kernel `y ↦ ⟨σ_xσ_y⟩^∞` is summable over `ℤ^d` for every basepoint
`x` (when `0 < contractionFactor < 1`).  The susceptibility
`∑_y ⟨σ_xσ_y⟩^∞` is finite and independent of the basepoint, since
`⟨σ_xσ_y⟩^∞ = ⟨σ_0σ_{y-x}⟩^∞` and summability is invariant under the
reindexing `y ↦ y - x`.  Part of Issue #2931. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_basepoint
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hcf_pos : 0 < contractionFactor d Λ p r) (hα : contractionFactor d Λ p r < 1)
    (x : Fin d → ℤ) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y}) := by
  have hbase :=
    correlationInfinite_latticeGraph_susceptibility_summable d hd r hr Λ p hf hh hcf_pos hα
  have heq :
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y})
        = (fun y =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y - x}) := by
    funext y
    rw [show ({x, y} : Finset (Fin d → ℤ)) = vaddFinset x {(0 : Fin d → ℤ), y - x} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact (correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ x p hf {(0 : Fin d → ℤ), y - x})
  rw [heq]
  exact ((Equiv.subRight x).summable_iff
    (f := fun z => correlationInfinite (IsingModel.latticeGraph d) Λ p
      {(0 : Fin d → ℤ), z})).mpr hbase

/-- **Unconditional strong-high-temperature uniform clustering**: in the explicit
regime `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the infinite-volume correlation is
uniformly small at large distance — for every `ε > 0` there is `R` with
`⟨σ_iσ_j⟩^∞ ≤ ε` for all pairs at distance `≥ R` — with no polynomial-decay
hypothesis (the contraction factor is `< 1` by
`contractionFactor_lt_one_of_high_temp`).  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_uniform_decay_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ∀ ε > (0 : ℝ), ∃ R : ℕ, ∀ i j : Fin d → ℤ,
      R ≤ IsingModel.latticeDistance d i j →
        correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} ≤ ε :=
  correlationInfinite_latticeGraph_uniform_decay_of_contractionFactor_lt_one
    d hd r hr Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Unconditional strong-high-temperature clustering (cofinite form)**: in the
explicit regime `βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the correlation kernel
`y ↦ ⟨σ_0σ_y⟩^∞` tends to `0` along the cofinite filter, with no polynomial-decay
hypothesis.  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_tendsto_cofinite_zero_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    Filter.Tendsto
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y})
      Filter.cofinite (nhds 0) :=
  correlationInfinite_latticeGraph_tendsto_cofinite_zero
    d hd r hr Λ p hf hh (contractionFactor_lt_one_of_high_temp d Λ p hf r hht)

/-- **Fully explicit unconditional high-temperature distance decay**: in the
regime `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, every distinct pair satisfies
`⟨σ_iσ_j⟩^∞ ≤ H^{dist(i,j)/(r+2)}` — a prefactor-free geometric decay with an
explicit base `H` depending only on `βJ`, `d`, `r` (no contraction factor in the statement and
no polynomial-decay hypothesis; the underlying ball-boundary shell-contraction
axiom `shellSup_contraction` (now a proven theorem) is still used).

The contraction factor is bounded by `H` (`contractionFactor_le_high_temp_const`)
and is `< 1` (`contractionFactor_lt_one_of_high_temp`), so the per-pair bound
`correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair` composes
with base monotonicity `cf^q ≤ H^q` (`pow_le_pow_left₀`).  Part of Issue #2931,
Phase 3a. -/
theorem correlationInfinite_latticeGraph_le_explicit_pow_dist
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
      ≤ (p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))))
          ^ (IsingModel.latticeDistance d i j / (r + 2)) := by
  have hcf_lt : contractionFactor d Λ p r < 1 :=
    contractionFactor_lt_one_of_high_temp d Λ p hf r hht
  have hbound :=
    correlationInfinite_latticeGraph_le_contractionFactor_pow_dist_pair
      d hd r hr Λ p hf hh hcf_lt hij
  have hmono :
      (contractionFactor d Λ p r) ^ (IsingModel.latticeDistance d i j / (r + 2))
        ≤ (p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))))
            ^ (IsingModel.latticeDistance d i j / (r + 2)) :=
    pow_le_pow_left₀ (contractionFactor_nonneg d Λ p hf r)
      (contractionFactor_le_high_temp_const d Λ p hf r) _
  exact hbound.trans hmono

/-- **Summability of the floor-power geometric lattice kernel**: for `0 < c < 1`,
the function `y ↦ c^{⌊dist(0,y)/(r+2)⌋}` is summable over `ℤ^d`.

It is dominated by `(1/c)·exp(-m·dist(0,y))` with `m = -log(c)/(r+2) > 0` (using
`c^{⌊q⌋} ≤ c^{q-1} = (1/c)·exp(-m·dist)`), and the exponential kernel is summable
by `summable_exp_neg_dist`.  This is the reusable core behind both the
contraction-factor and explicit-base susceptibility bounds (Issue #2931). -/
theorem summable_pow_div_latticeDistance (d r : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Summable (fun y : Fin d → ℤ => c ^ (IsingModel.latticeDistance d 0 y / (r + 2))) := by
  set m := -Real.log c / (r + 2 : ℝ) with hmdef
  have hr2_pos : (0 : ℝ) < (r + 2 : ℝ) := by positivity
  have hlog_neg : Real.log c < 0 := Real.log_neg hc0 hc1
  have hm_pos : 0 < m := by rw [hmdef]; exact div_pos (by linarith [hlog_neg]) hr2_pos
  have hmaj_sum :
      Summable (fun y : Fin d → ℤ =>
        (1 / c) * Real.exp (-m * (IsingModel.latticeDistance d 0 y : ℝ))) :=
    (summable_exp_neg_dist hm_pos d 0).mul_left (1 / c)
  refine Summable.of_nonneg_of_le (fun y => pow_nonneg hc0.le _) (fun y => ?_) hmaj_sum
  set n := IsingModel.latticeDistance d 0 y with hndef
  have hq_real : ((n / (r + 2) : ℕ) : ℝ) ≥ (n : ℝ) / (r + 2 : ℝ) - 1 := by
    have hlt : n < (n / (r + 2) + 1) * (r + 2) := by
      have hmod := Nat.mod_lt n (show 0 < r + 2 by omega)
      have hdm := Nat.div_add_mod n (r + 2)
      nlinarith [hmod, hdm]
    have hcast : (n : ℝ) < (((n / (r + 2) : ℕ) : ℝ) + 1) * ((r : ℝ) + 2) := by
      have := (Nat.cast_lt (α := ℝ)).2 hlt
      push_cast at this; linarith [this]
    rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hr2_pos]
    nlinarith [hcast]
  have hstep1 : c ^ (n / (r + 2)) ≤ c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := by
    rw [← Real.rpow_natCast c (n / (r + 2))]
    exact Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le hq_real
  have hstep2 :
      c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) = (1 / c) * Real.exp (-m * (n : ℝ)) := by
    rw [Real.rpow_sub hc0, Real.rpow_one, Real.rpow_def_of_pos hc0,
      one_div, div_eq_mul_inv, mul_comm (c⁻¹) (Real.exp (-m * (n : ℝ)))]
    congr 1
    congr 1
    rw [hmdef]; ring
  calc c ^ (n / (r + 2)) ≤ c ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := hstep1
    _ = (1 / c) * Real.exp (-m * (n : ℝ)) := hstep2

/-- **Unconditional finite susceptibility at strong high temperature**: under
`0 < βJ` and the explicit condition `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the
correlation kernel `y ↦ ⟨σ_0σ_y⟩^∞` is summable (finite susceptibility), with no
polynomial-decay hypothesis and no contraction-factor positivity.

The explicit decay `correlationInfinite_latticeGraph_le_explicit_pow_dist`
dominates the kernel by `H^{dist(0,y)/(r+2)}` with `0 < H < 1`, which is summable
by `summable_pow_div_latticeDistance`.  Part of Issue #2931, Phase 3a. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hβJ_pos : 0 < p.β * p.J)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y}) := by
  set H := p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) with hHdef
  have hH_pos : 0 < H := by
    rw [hHdef]
    have : (0 : ℝ) < 2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)) := by positivity
    exact mul_pos hβJ_pos this
  have hmaj : Summable (fun y : Fin d → ℤ =>
      H ^ (IsingModel.latticeDistance d 0 y / (r + 2))) :=
    summable_pow_div_latticeDistance d r hH_pos hht
  refine Summable.of_nonneg_of_le
    (fun y => correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _)
    (fun y => ?_) hmaj
  by_cases hy : y = 0
  · subst hy
    have hone : correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), 0} ≤ 1 :=
      correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p _
    rw [IsingModel.latticeDistance_self]
    simpa using hone
  · exact correlationInfinite_latticeGraph_le_explicit_pow_dist d hd r hr Λ p hf hh hht
      (Ne.symm hy)

/-- **Unconditional finite susceptibility from any basepoint at high
temperature**: by translation invariance, the correlation kernel
`y ↦ ⟨σ_xσ_y⟩^∞` is summable for every basepoint `x` under `0 < βJ` and
`H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`.  The susceptibility is finite and
basepoint-independent, with no polynomial-decay hypothesis.  Part of Issue #2931,
Phase 3a. -/
theorem correlationInfinite_latticeGraph_susceptibility_summable_high_temp_basepoint
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (hβJ_pos : 0 < p.β * p.J)
    (hht : p.β * p.J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1)
    (x : Fin d → ℤ) :
    Summable
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y}) := by
  have hbase :=
    correlationInfinite_latticeGraph_susceptibility_summable_high_temp
      d hd r hr Λ p hf hh hβJ_pos hht
  have heq :
      (fun y => correlationInfinite (IsingModel.latticeGraph d) Λ p {x, y})
        = (fun y =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), y - x}) := by
    funext y
    rw [show ({x, y} : Finset (Fin d → ℤ)) = vaddFinset x {(0 : Fin d → ℤ), y - x} from by
      rw [vaddFinset_pair]; simp [vadd_eq_add]]
    exact (correlationInfinite_vaddFinset_of_translationInvariant
      (IsingModel.latticeGraph d) Λ x p hf {(0 : Fin d → ℤ), y - x})
  rw [heq]
  exact ((Equiv.subRight x).summable_iff
    (f := fun z => correlationInfinite (IsingModel.latticeGraph d) Λ p
      {(0 : Fin d → ℤ), z})).mpr hbase

end Ambient
end IsingModel
