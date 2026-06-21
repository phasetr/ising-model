import IsingModel.ClusterExpansion.MayerCore.TermsComplexPerSiteBound
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.Concrete.CubicFreeEnergy

/-!
# Per-site complex cluster free energy over the cubic exhaustion (GJ §18.6)

This file packages the **per-site complex cluster free energy**
`F_n(z) := (∑'_k mayerExpansionTermComplex (inducedGraph (latticeGraph d) (cubicBox d n)) k z)
  / (cubicBox d n).card`
along the cubic exhaustion of `ℤ^d`, together with its holomorphy and a **ball-uniform** norm
bound.  This is the analytic input for the Montel/Vitali infinite-volume limit (PR-D2.3b-d of
Issue #4149): a locally bounded sequence of holomorphic functions on a fixed ball, hence a normal
family with a holomorphic limit.

## Main definitions and results

* `cubicMayerClusterFreeEnergyComplex` — the per-site complex cluster free energy `F_n`.
* `cubicMayerClusterFreeEnergyComplex_differentiableOn` — `F_n` is `DifferentiableOn ℂ` on
  `ball 0 R` whenever `(2d)²eR` lies in the Kotecky--Preiss region.
* `cubicMayerClusterFreeEnergyComplex_analyticOnNhd` — the corresponding `AnalyticOnNhd`.
* `cubicMayerClusterFreeEnergyComplex_norm_le` — `‖F_n(z)‖ ≤ kpBound (2d) R` for `z ∈ ball 0 R`,
  a bound **independent of the stage `n` and of `z` in the ball**.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.6 (cluster expansion, analyticity).

## Supporting lemmas

* `mayerExpansionTermComplex_tsum_differentiableOn_ball` (holomorphy of the complex Mayer series).
* `latticeGraph_kp_tsum_complex_per_site_le_on_ball` (ball-uniform per-site norm bound).
* `induced_latticeGraph_maxDegree_le`, `kpRegion_downward_closed` (maximum-degree KP discharge).
* `mayerExpansionTermComplex_zero` (vanishing of the `k = 0` term).
* `card_cubicBox`, `cubicBox_nonempty`.
-/

namespace IsingModel

open Ambient

/-- **Per-site complex cluster free energy over the cubic exhaustion (GJ §18.6).**
`F_n(z) := (∑'_k mayerExpansionTermComplex (inducedGraph (latticeGraph d) (cubicBox d n)) k z)
  / (cubicBox d n).card`, the volume-averaged complex cluster free energy at stage `n` of the
cubic exhaustion of `ℤ^d`.  Here `(cubicBox d n).card = (2n+1)^d > 0` (`card_cubicBox`), cast to
`ℂ` for the division. -/
noncomputable def cubicMayerClusterFreeEnergyComplex (d n : ℕ) (z : ℂ) : ℂ :=
  (∑' k : ℕ, mayerExpansionTermComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)) k z)
    / ((cubicBox d n).card : ℂ)

/-- **Holomorphy of the per-site complex cluster free energy (GJ §18.6).**  If `0 ≤ R` and
`(2d)²eR` lies in the Kotecky--Preiss region — `(2d)²eR < 1` and `4(2d)²eR/(1−(2d)²eR)² < 1` —
then `z ↦ cubicMayerClusterFreeEnergyComplex d n z` is `DifferentiableOn ℂ` on `ball 0 R`.

The complex Mayer series `z ↦ ∑'_k mayerExpansionTermComplex G k z` is holomorphic on the ball
(`mayerExpansionTermComplex_tsum_differentiableOn_ball`); its KP hypotheses are stated for the
actual maximum degree `G.maxDegree`, discharged from the `2d` ones via
`induced_latticeGraph_maxDegree_le` and `kpRegion_downward_closed`.  Division by the constant
`((cubicBox d n).card : ℂ)` preserves differentiability (`DifferentiableOn.div_const`). -/
theorem cubicMayerClusterFreeEnergyComplex_differentiableOn (d n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    DifferentiableOn ℂ (fun z => cubicMayerClusterFreeEnergyComplex d n z)
      (Metric.ball (0 : ℂ) R) := by
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d) (cubicBox d n) with hG
  -- Discharge the actual-maximum-degree KP hypotheses from the `2d` ones.
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d (cubicBox d n)
  have heR : (0 : ℝ) ≤ Real.exp 1 * R := by positivity
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by positivity
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) := by
    apply mul_le_mul_of_nonneg_right _ heR
    have hcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
    gcongr
  obtain ⟨hkpG, hρG⟩ := kpRegion_downward_closed h0 h12 hkp2dR hρ2dR
  -- Holomorphy of the complex Mayer series, then divide by the constant volume.
  have hdiff := mayerExpansionTermComplex_tsum_differentiableOn_ball G hR hkpG hρG
  exact hdiff.div_const _

/-- **Analyticity of the per-site complex cluster free energy (GJ §18.6).**  Under the same
Kotecky--Preiss hypotheses as `cubicMayerClusterFreeEnergyComplex_differentiableOn`,
`z ↦ cubicMayerClusterFreeEnergyComplex d n z` is `AnalyticOnNhd ℂ` on `ball 0 R`.  Immediate
from holomorphy on the open ball (`DifferentiableOn.analyticOnNhd`). -/
theorem cubicMayerClusterFreeEnergyComplex_analyticOnNhd (d n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    AnalyticOnNhd ℂ (fun z => cubicMayerClusterFreeEnergyComplex d n z)
      (Metric.ball (0 : ℂ) R) :=
  (cubicMayerClusterFreeEnergyComplex_differentiableOn d n hR hkp2dR hρ2dR).analyticOnNhd
    Metric.isOpen_ball

/-- **Ball-uniform norm bound on the per-site complex cluster free energy (GJ §18.6).**  For
`z ∈ ball 0 R` with `(2d)²eR` in the Kotecky--Preiss region,
`‖cubicMayerClusterFreeEnergyComplex d n z‖ ≤ kpBound (2 d) R`, a bound **independent of the stage
`n` and of `z` in the ball** — exactly the local uniform bound needed for Montel/Vitali.

Since the `k = 0` complex Mayer term vanishes (`mayerExpansionTermComplex_zero`), the full series
equals the shifted one, so `‖∑'_k full‖ ≤ ∑'_k ‖succ‖` (`norm_tsum_le_tsum_norm`).  Dividing by
`‖(card : ℂ)‖ = (card : ℝ)` (`Complex.norm_natCast`, `Fintype.card_coe`) gives the per-site norm,
bounded by `latticeGraph_kp_tsum_complex_per_site_le_on_ball`. -/
theorem cubicMayerClusterFreeEnergyComplex_norm_le (d n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖cubicMayerClusterFreeEnergyComplex d n z‖ ≤ kpBound (2 * d) R := by
  classical
  haveI : Nonempty (↑(cubicBox d n) : Type _) := (cubicBox_nonempty d n).to_subtype
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d) (cubicBox d n) with hG
  -- KP discharge at the actual maximum degree, at radius `‖z‖`.
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d (cubicBox d n)
  have hzlt : ‖z‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hz
  have hzle : ‖z‖ ≤ R := le_of_lt hzlt
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hez : (0 : ℝ) ≤ Real.exp 1 * ‖z‖ := by positivity
  have hr2dz : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) := by gcongr
  have h0_2dz : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by positivity
  obtain ⟨hkp2dz, hρ2dz⟩ := kpRegion_downward_closed h0_2dz hr2dz hkp2dR hρ2dR
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by
    apply mul_le_mul_of_nonneg_right _ hez
    have hcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
    gcongr
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) := by positivity
  obtain ⟨hkpG, hρG⟩ := kpRegion_downward_closed h0 h12 hkp2dz hρ2dz
  -- Volume cardinality is positive.
  have hcardpos : 0 < (cubicBox d n).card := (cubicBox_nonempty d n).card_pos
  have hcardR : (0 : ℝ) < ((cubicBox d n).card : ℝ) := by exact_mod_cast hcardpos
  -- `∑'_k full = ∑'_k succ`, since the `k = 0` term vanishes.
  have hsucc : Summable fun k : ℕ => ‖mayerExpansionTermComplex G (k + 1) z‖ :=
    summable_norm_mayerExpansionTermComplex_succ_of_tail_condition G hkpG hρG
  have hsum : Summable fun k : ℕ => mayerExpansionTermComplex G k z :=
    (summable_nat_add_iff 1).mp hsucc.of_norm
  have hshift : (∑' k : ℕ, mayerExpansionTermComplex G k z)
      = ∑' k : ℕ, mayerExpansionTermComplex G (k + 1) z := by
    rw [hsum.tsum_eq_zero_add, mayerExpansionTermComplex_zero, zero_add]
  have hnorm : ‖∑' k : ℕ, mayerExpansionTermComplex G k z‖
      ≤ ∑' k : ℕ, ‖mayerExpansionTermComplex G (k + 1) z‖ := by
    rw [hshift]; exact norm_tsum_le_tsum_norm hsucc
  -- The shifted per-site sum is bounded by `kpBound (2d) R` (ball-uniform).
  have hmain := latticeGraph_kp_tsum_complex_per_site_le_on_ball d (cubicBox d n) hR
    hkp2dR hρ2dR hz
  rw [Fintype.card_coe] at hmain
  -- Unfold `F_n` and rewrite the complex cardinality norm into the real cardinality.
  unfold cubicMayerClusterFreeEnergyComplex
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hcardR]
  refine hnorm.trans ?_
  rw [← div_le_iff₀ hcardR]
  exact hmain

end IsingModel
