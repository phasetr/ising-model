import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallBoundaryInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd
import IsingModel.Concrete.LatticeSphereCard
import IsingModel.TranslationInvariance.Truncated
import IsingModel.LatticeExpSum

/-!
# Theorem eta-le-1 split — Phase 5: contraction factor

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

end Ambient
end IsingModel
