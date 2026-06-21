import IsingModel.ClusterExpansion.MayerCore.TermsComplexHolomorphic
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Volume-uniform (per-site) bound on the complex Mayer expansion sum (GJ §18.6)

The complex-norm analogue of the real volume-uniform per-site Mayer bound
(`tsum_abs_mayerExpansionTerm_succ_div_card_le`, #4137, and its ℤ^d ball-uniform lift
`latticeGraph_kp_tsum_per_site_le`, #4148): dividing the explicit bound on the total
shifted complex Mayer expansion sum by the volume `|V| = Fintype.card ι` gives a
**volume-uniform** (per-site) bound.  For `r = Δ²e‖z‖`, `Δ²e‖z‖ < 1`,
`ρ = 4r/(1−r)² < 1`, and a nonempty vertex type,

`(∑'_n ‖mayerExpansionTermComplex G (n + 1) z‖)/|V| ≤ kpBound Δ ‖z‖`,

with a right-hand side independent of the volume.  The `n = 0` term vanishes
(`mayerExpansionTermComplex_zero`), so the same per-site constant also bounds the full
series via `‖∑'_n‖ ≤ ∑'_n ‖·‖` (`tsum_norm_mayerExpansionTermComplex_div_card_le`).

On the lattice `latticeGraph d` induced on a finite box `Λ`, the maximum degree is bounded
by `2 d`, and the bound is uniform both over the volume `Λ` and over `z` in a ball of radius
`R` in the Kotecky--Preiss region: `latticeGraph_kp_tsum_complex_per_site_le_on_ball`.  This
ball-uniform per-site bound is the input for the Montel/Vitali infinite-volume holomorphic
limit of the per-site complex cluster free energy.

* `mayerExpansionTermComplex_zero`.
* `summable_norm_mayerExpansionTermComplex_succ_of_tail_condition`.
* `tsum_norm_mayerExpansionTermComplex_succ_le`.
* `tsum_norm_mayerExpansionTermComplex_succ_div_card_le`.
* `tsum_norm_mayerExpansionTermComplex_div_card_le`.
* `latticeGraph_kp_tsum_complex_per_site_le_on_ball`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.5--§18.6, pp.~335--340.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `n = 0` complex Mayer term vanishes**: `mayerExpansionTermComplex G 0 z = 0`.
The unique `ω : Fin 0 → polymers` is the empty function; the incompatibility graph on
`Fin 0` is disconnected (`Connected` requires `Nonempty`), so `ursellCoefficient empty = 0`
and its complex cast is `0`.  The complex analogue of `mayerExpansionTerm_zero`. -/
theorem mayerExpansionTermComplex_zero (G : SimpleGraph ι) [Fintype G.edgeSet] (z : ℂ) :
    mayerExpansionTermComplex G 0 z = 0 := by
  unfold mayerExpansionTermComplex
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  refine mul_eq_zero.mpr (Or.inl ?_)
  rw [Complex.ofReal_eq_zero]
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h
  exact (h.nonempty.elim Fin.elim0)

/-- **Norm-summability of the shifted complex Mayer expansion terms.**  If `Δ²e‖z‖ < 1` and
`4·Δ²e‖z‖/(1−Δ²e‖z‖)² < 1`, then `n ↦ ‖mayerExpansionTermComplex G (n + 1) z‖` is summable.
The geometric majorant `|V|/(1−r)·(4r/(1−r)²)^n`
(`mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric`) is summable since its ratio
is `< 1`.  The complex-norm analogue of
`summable_abs_mayerExpansionTerm_succ_of_tail_condition`. -/
theorem summable_norm_mayerExpansionTermComplex_succ_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2 < 1) :
    Summable fun n : ℕ => ‖mayerExpansionTermComplex G (n + 1) z‖ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hgeo : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeo
  exact mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric G n hkp

/-- **Explicit bound on the shifted complex Mayer expansion sum.**  Summing the geometric
per-order norm bound (`mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric`) gives
`∑'_n ‖mayerExpansionTermComplex G (n + 1) z‖ ≤ |V|/((1−r)(1−ρ))` with `r = Δ²e‖z‖` and
`ρ = 4r/(1−r)²`, under `Δ²e‖z‖ < 1` and `ρ < 1`.  The complex-norm analogue of
`tsum_abs_mayerExpansionTerm_succ_le`. -/
theorem tsum_norm_mayerExpansionTermComplex_succ_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2 < 1) :
    (∑' n : ℕ, ‖mayerExpansionTermComplex G (n + 1) z‖)
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2)⁻¹ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hsummL : Summable fun n : ℕ => ‖mayerExpansionTermComplex G (n + 1) z‖ :=
    summable_norm_mayerExpansionTermComplex_succ_of_tail_condition G hkp hρ
  have hsummR : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  calc (∑' n : ℕ, ‖mayerExpansionTermComplex G (n + 1) z‖)
      ≤ ∑' n : ℕ, (Fintype.card ι : ℝ) / q * ρ ^ n :=
        hsummL.tsum_le_tsum
          (fun n => mayerExpansionTermComplex_succ_norm_le_card_div_mul_geometric G n hkp) hsummR
    _ = (Fintype.card ι : ℝ) / q * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ]

/-- **Volume-uniform (per-site) bound on the complex Mayer expansion sum.**  For a nonempty
vertex type, `Δ²e‖z‖ < 1`, and `ρ := 4Δ²e‖z‖/(1−Δ²e‖z‖)² < 1`, the per-site total complex
Mayer expansion norm sum is bounded by the volume-uniform constant `kpBound Δ ‖z‖`
(`= ((1−r)(1−ρ))⁻¹`, `r = Δ²e‖z‖`):
`(∑'_n ‖mayerExpansionTermComplex G (n + 1) z‖)/|V| ≤ kpBound Δ ‖z‖`.  Dividing
`tsum_norm_mayerExpansionTermComplex_succ_le` by `|V|`.  The complex-norm analogue of
`tsum_abs_mayerExpansionTerm_succ_div_card_le`. -/
theorem tsum_norm_mayerExpansionTermComplex_succ_div_card_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2 < 1) :
    (∑' n : ℕ, ‖mayerExpansionTermComplex G (n + 1) z‖) / (Fintype.card ι : ℝ)
      ≤ kpBound (G.maxDegree) ‖z‖ := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρpos : 0 < 1 - ρ := by linarith [hρ]
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have habs : |‖z‖| = ‖z‖ := abs_of_nonneg (norm_nonneg z)
  rw [div_le_iff₀ hcard, kpBound, habs]
  -- `∑' ≤ |V|/q·(1−ρ)⁻¹ = (q(1−ρ))⁻¹·|V|`.
  refine (tsum_norm_mayerExpansionTermComplex_succ_le G hkp hρ).trans ?_
  rw [mul_inv]
  rw [div_mul_eq_mul_div, mul_comm, ← div_eq_mul_inv, mul_div_assoc]
  exact le_of_eq (by ring)

/-- **Volume-uniform (per-site) bound on the full complex Mayer expansion sum.**  Since the
`n = 0` complex Mayer term vanishes (`mayerExpansionTermComplex_zero`), the full series equals
the shifted one, and `‖∑'_n‖ ≤ ∑'_n ‖·‖` (`norm_tsum_le_tsum_norm`), so the same per-site
constant `kpBound Δ ‖z‖` bounds the per-site norm of the full Mayer expansion sum:
`‖∑'_n mayerExpansionTermComplex G n z‖/|V| ≤ kpBound Δ ‖z‖`. -/
theorem tsum_norm_mayerExpansionTermComplex_div_card_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2 < 1) :
    ‖∑' n : ℕ, mayerExpansionTermComplex G n z‖ / (Fintype.card ι : ℝ)
      ≤ kpBound (G.maxDegree) ‖z‖ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsucc : Summable fun n : ℕ => ‖mayerExpansionTermComplex G (n + 1) z‖ :=
    summable_norm_mayerExpansionTermComplex_succ_of_tail_condition G hkp hρ
  have hsum : Summable fun n : ℕ => mayerExpansionTermComplex G n z :=
    (summable_nat_add_iff 1).mp hsucc.of_norm
  -- shift the Mayer series to drop the vanishing `n = 0` term.
  have hshift : (∑' n : ℕ, mayerExpansionTermComplex G n z)
      = ∑' n : ℕ, mayerExpansionTermComplex G (n + 1) z := by
    rw [hsum.tsum_eq_zero_add, mayerExpansionTermComplex_zero, zero_add]
  -- bound the norm of the tsum by the tsum of norms.
  have hnorm : ‖∑' n : ℕ, mayerExpansionTermComplex G n z‖
      ≤ ∑' n : ℕ, ‖mayerExpansionTermComplex G (n + 1) z‖ := by
    rw [hshift]
    exact norm_tsum_le_tsum_norm hsucc
  rw [div_le_iff₀ hcard]
  refine hnorm.trans ?_
  rw [← div_le_iff₀ hcard]
  exact tsum_norm_mayerExpansionTermComplex_succ_div_card_le G hkp hρ

/-- **ℤ^d ball-uniform per-site complex Mayer bound** (headline).  For the lattice graph
`latticeGraph d` induced on a finite box `Λ` and `z` in the ball of radius `R` (with `(2d)²eR`
in the Kotecky--Preiss region), the per-site total complex Mayer expansion norm sum is bounded
by `kpBound (2 d) R`, a constant **independent of the volume `Λ` and of `z` in the ball**.

The actual maximum degree of the induced lattice graph is at most `2 d`
(`induced_latticeGraph_maxDegree_le`).  Since `z ∈ ball 0 R` gives `‖z‖ < R`, the KP
hypotheses at `‖z‖` are discharged from the `2d`/`R` ones by `kpRegion_downward_closed`; the
abstract per-site bound `tsum_norm_mayerExpansionTermComplex_succ_div_card_le` gives
`≤ kpBound (maxDegree) ‖z‖`, dominated by `kpBound (2d) ‖z‖`
(`kpBound_mono_of_degree_le`) and then by `kpBound (2d) R` (`kpBound_r_mono_of_le`). -/
theorem latticeGraph_kp_tsum_complex_per_site_le_on_ball (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)] {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    (∑' n : ℕ, ‖mayerExpansionTermComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (n + 1) z‖)
      / (Fintype.card (↑Λ : Type _) : ℝ)
      ≤ kpBound (2 * d) R := by
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d) Λ with hG
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d Λ
  -- `z ∈ ball 0 R ⟹ ‖z‖ < R` and `0 ≤ ‖z‖`.
  have hzlt : ‖z‖ < R := by
    rwa [Metric.mem_ball, dist_zero_right] at hz
  have hzle : ‖z‖ ≤ R := le_of_lt hzlt
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- Translate the `(2d, R)` KP region to the `(2d, ‖z‖)` region.
  have hexp : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hr2dz : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
  have h0_2dz : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by positivity
  obtain ⟨hkp2dz, hρ2dz⟩ := kpRegion_downward_closed h0_2dz hr2dz hkp2dR hρ2dR
  -- `r = maxDegree²e‖z‖ ≤ (2d)²e‖z‖`.
  have he : (0 : ℝ) ≤ Real.exp 1 * ‖z‖ := by positivity
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by
    apply mul_le_mul_of_nonneg_right _ he
    have hcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
    gcongr
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by positivity
  -- discharge the actual-maxDegree KP hypotheses from the `2d`-at-`‖z‖` ones.
  obtain ⟨hkp, hρ⟩ := kpRegion_downward_closed h0 h12 hkp2dz hρ2dz
  -- apply the abstract per-site complex bound at the actual maximum degree.
  have hmain := tsum_norm_mayerExpansionTermComplex_succ_div_card_le G hkp hρ
  refine hmain.trans ?_
  -- restate the `2d`-at-`‖z‖` KP hypotheses with `|‖z‖|` for `kpBound_mono_of_degree_le`.
  have habsz : |‖z‖| = ‖z‖ := abs_of_nonneg hznn
  have hkp2dz' : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|) < 1 := by rw [habsz]; exact hkp2dz
  have hρ2dz' : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|))
      / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|)) ^ 2 < 1 := by rw [habsz]; exact hρ2dz
  -- dominate by `kpBound (2d) ‖z‖` (degree monotonicity), then by `kpBound (2d) R` (r-mono).
  refine (kpBound_mono_of_degree_le hΔ ‖z‖ hkp2dz' hρ2dz').trans ?_
  -- `kpBound (2d) ‖z‖ ≤ kpBound (2d) R` via `kpBound_r_mono_of_le` on the `r`-variable form.
  have hrR2 : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1 := hkp2dR
  have hρR2 : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
      / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1 := hρ2dR
  have hmono := kpBound_r_mono_of_le h0_2dz hr2dz hrR2 hρR2
  -- rewrite `kpBound` in the `r`-variable form and apply `hmono`, noting `|‖z‖| = ‖z‖`, `|R| = R`.
  rw [kpBound, kpBound, abs_of_nonneg hznn, abs_of_nonneg hR]
  exact hmono

end IsingModel
