import IsingModel.ClusterExpansion.MayerCore.CubicMayerClusterFreeEnergyComplex
import IsingModel.ComplexAnalyticity.ClosureCompactness
import IsingModel.AmbientComplexAnalyticity.AscoliData.Constructors.AnalyticSideConditions

/-!
# Montel compact carrier for the per-site complex cluster free energy (GJ §18.6)

This file performs the **Montel step** (PR-D2.3b of Issue #4149) for the per-site complex cluster
free energies `F_n(z) := cubicMayerClusterFreeEnergyComplex d n z` over the cubic exhaustion of
`ℤ^d`.  The sequence `F_n` is holomorphic on `ball 0 R` (D2.3a
`cubicMayerClusterFreeEnergyComplex_analyticOnNhd`) and uniformly bounded there by `kpBound (2d) R`
(D2.3a `cubicMayerClusterFreeEnergyComplex_norm_le`), so by Arzelà--Ascoli the restrictions form a
relatively compact family in the compact-open space `C(↑(ball 0 R), ℂ)`.  The resulting compact
carrier is the input to the subsequence extraction (D2.3d).

## Main definitions and results

* `kpBound_nonneg_of_kpRegion` — the Kotecky--Preiss bound constant is nonnegative on its region.
* `cubicMayerClusterFreeEnergyComplexRestrict` — the restriction of `F_n` as a `ContinuousMap` on
  the subtype ball.
* `cubicMayerClusterFreeEnergyComplex_equicontinuous` — equicontinuity of the family.
* `cubicMayerClusterFreeEnergyComplex_exists_compact_carrier` — the Montel headline: a compact set
  `A ⊆ C(↑(ball 0 R), ℂ)` containing every restricted `F_n`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.6 (cluster expansion, analyticity).
-/

namespace IsingModel

/-- **Nonnegativity of the Kotecky--Preiss bound constant on its region.**  With
`r = Δ²·e·|t|`, the constant `kpBound Δ t = ((1−r)(1−ρ))⁻¹` where `ρ = 4r/(1−r)²`.  In the KP
region `r < 1` (so `1 − r > 0`) and `ρ < 1` (so `1 − ρ > 0`), the product of the two factors is
positive, hence its inverse is positive — in particular nonnegative. -/
theorem kpBound_nonneg_of_kpRegion {Δ : ℕ} {t : ℝ}
    (hkp : (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((Δ : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    0 ≤ kpBound Δ t := by
  unfold kpBound
  have h1 : (0 : ℝ) < 1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|) := by linarith
  have h2 : (0 : ℝ) < 1 - 4 * ((Δ : ℝ) ^ 2 * (Real.exp 1 * |t|))
      / (1 - (Δ : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 := by linarith
  positivity

/-- **Restriction of the per-site complex cluster free energy to the subtype ball.**  Under the
Kotecky--Preiss hypotheses, `F_n` is analytic, hence continuous on `ball 0 R`; its restriction to
the subtype `↑(ball 0 R)` is a `ContinuousMap`.  This packages the family for the compact-open
Montel/Vitali machinery. -/
noncomputable def cubicMayerClusterFreeEnergyComplexRestrict (d n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    C(↑(Metric.ball (0 : ℂ) R), ℂ) :=
  ⟨(Metric.ball (0 : ℂ) R).restrict (fun z => cubicMayerClusterFreeEnergyComplex d n z),
    ((cubicMayerClusterFreeEnergyComplex_analyticOnNhd d n hR hkp2dR hρ2dR).continuousOn).restrict⟩

/-- The restriction agrees with the per-site complex cluster free energy on the ball. -/
theorem cubicMayerClusterFreeEnergyComplexRestrict_apply (d n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    cubicMayerClusterFreeEnergyComplexRestrict d n hR hkp2dR hρ2dR ⟨z, hz⟩
      = cubicMayerClusterFreeEnergyComplex d n z := rfl

/-- **Equicontinuity of the per-site complex cluster free energy family on the ball (GJ §18.6).**
Each `F_n` is analytic on `ball 0 R` and uniformly bounded there by `kpBound (2d) R`
(independently of `n`).  The Schwarz/Cauchy derivative estimate then yields a uniform local
Lipschitz bound, hence equicontinuity of the family
`equicontinuous_restrict_of_analyticOnNhd_of_bounded`. -/
theorem cubicMayerClusterFreeEnergyComplex_equicontinuous (d : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    Equicontinuous (fun n (z : ↑(Metric.ball (0 : ℂ) R)) =>
      cubicMayerClusterFreeEnergyComplex d n (z : ℂ)) := by
  have hCnn : (0 : ℝ) ≤ kpBound (2 * d) R := by
    have habs : |R| = R := abs_of_nonneg hR
    refine kpBound_nonneg_of_kpRegion (Δ := 2 * d) (t := R) ?_ ?_
    · rwa [habs]
    · rwa [habs]
  exact equicontinuous_restrict_of_analyticOnNhd_of_bounded hCnn
    (fun n => cubicMayerClusterFreeEnergyComplex_analyticOnNhd d n hR hkp2dR hρ2dR)
    (fun n z hz => cubicMayerClusterFreeEnergyComplex_norm_le d n hR hkp2dR hρ2dR hz)

/-- **Montel compact carrier for the per-site complex cluster free energy (GJ §18.6).**  Under the
Kotecky--Preiss hypotheses on `ball 0 R`, there is a compact set `A ⊆ C(↑(ball 0 R), ℂ)`
containing the restriction `Fc n` of every per-site complex cluster free energy `F_n`, with
`Fc n` agreeing with `F_n` on the ball.

The carrier is `A := toFun ⁻¹' closure (toFun '' (range Fc))`, compact by
`isCompact_closureCarrier_compactOpen_complex_of_norm_le_equicontinuous` with constant target
`kpBound (2d) R`: the pointwise norm bound is the D2.3a bound, and the set equicontinuity of the
range carrier is the family equicontinuity re-indexed via `equicontinuous_range_coe`.  Membership
holds because every `Fc n` lies in `range Fc`, whose image sits inside its closure. -/
theorem cubicMayerClusterFreeEnergyComplex_exists_compact_carrier (d : ℕ) {R : ℝ} (hR : 0 < R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    ∃ A : Set C(↑(Metric.ball (0 : ℂ) R), ℂ), IsCompact A ∧
      ∃ Fc : ℕ → C(↑(Metric.ball (0 : ℂ) R), ℂ), (∀ n, Fc n ∈ A) ∧
        (∀ n, ∀ z (hz : z ∈ Metric.ball (0 : ℂ) R),
          cubicMayerClusterFreeEnergyComplex d n z = Fc n ⟨z, hz⟩) := by
  classical
  set Fc : ℕ → C(↑(Metric.ball (0 : ℂ) R), ℂ) :=
    fun n => cubicMayerClusterFreeEnergyComplexRestrict d n hR.le hkp2dR hρ2dR with hFc
  set S : Set C(↑(Metric.ball (0 : ℂ) R), ℂ) := Set.range Fc with hS
  set A : Set C(↑(Metric.ball (0 : ℂ) R), ℂ) :=
    ContinuousMap.toFun ⁻¹' closure (ContinuousMap.toFun '' S) with hA
  -- Set equicontinuity of the range carrier from the family equicontinuity.
  have hSeq : Equicontinuous ((↑) : S → ↑(Metric.ball (0 : ℂ) R) → ℂ) := by
    refine equicontinuous_range_coe Fc ?_
    exact cubicMayerClusterFreeEnergyComplex_equicontinuous d hR.le hkp2dR hρ2dR
  -- Pointwise norm bound for every member of `S`.
  have hnorm : ∀ f ∈ S, ∀ x : ↑(Metric.ball (0 : ℂ) R),
      ‖f x‖ ≤ (fun _ : ↑(Metric.ball (0 : ℂ) R) => kpBound (2 * d) R) x := by
    rintro f ⟨n, rfl⟩ x
    have hxmem : (x : ℂ) ∈ Metric.ball (0 : ℂ) R := x.2
    change ‖cubicMayerClusterFreeEnergyComplex d n (x : ℂ)‖ ≤ kpBound (2 * d) R
    exact cubicMayerClusterFreeEnergyComplex_norm_le d n hR.le hkp2dR hρ2dR hxmem
  have hAcompact : IsCompact A :=
    isCompact_closureCarrier_compactOpen_complex_of_norm_le_equicontinuous
      (fun _ : ↑(Metric.ball (0 : ℂ) R) => kpBound (2 * d) R) hnorm hSeq
  refine ⟨A, hAcompact, Fc, ?_, ?_⟩
  · intro n
    have hmemS : Fc n ∈ S := Set.mem_range_self n
    have himg : ContinuousMap.toFun (Fc n) ∈ ContinuousMap.toFun '' S :=
      ⟨Fc n, hmemS, rfl⟩
    exact subset_closure himg
  · intro n z hz
    rw [hFc]
    rfl

end IsingModel
