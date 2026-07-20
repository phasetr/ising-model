import IsingModel.HLSConvolutionSharp.ShellSumsIntegralComparison

/-!
# Sharp HLS convolution (2/3): radial ball/tail sums and the three-region cover

Structural split (2/3) of `HLSConvolutionSharp`.  This child holds the radial shell-sum
and lattice `ℝ≥0∞` sum bounds over a ball (`α < d`) and over a tail (`d < 2α`), the
resulting near-`x` and far region bounds of the sharp HLS convolution, and the
three-region cover `tsum_conv_le_sum_regions` of the full convolution sum.  It builds on
the shell reorganization and integral comparisons in the sibling
`...ShellSumsIntegralComparison`; the constant reduction and the headline theorem live in
`...ConstantReductionCapstone`.  See the `HLSConvolutionSharp` facade module for the full
contents overview.
-/

namespace IsingModel

open scoped ENNReal
open Ambient

/-- **Radial shell-sum over a ball** (`α < d`, `d ≥ 1`): the shell-weighted
inverse-power sum over radii `0..K` is bounded by `2^d·((K+2)^{d-α}/(d-α) + 1)`.

Combines `latticeSphere_card_mul_rpow_le` (term-wise card→power reduction, with
`s = -α`) with the head-sum integral comparison `sum_Ioc_zero_nat_rpow_le` (at
`e = d-1-α > -1`), after reindexing `∑_{n ∈ range (K+1)} (1+n)^e = ∑_{m ∈ Ioc 0 (K+1)} m^e`. -/
theorem radial_shell_ball_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < (d : ℝ))
    (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1),
        ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)
      ≤ (2 : ℝ) ^ d * (((K : ℝ) + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1) := by
  set e : ℝ := (d : ℝ) - 1 - α with he_def
  have he : -1 < e := by rw [he_def]; linarith
  -- Term-wise card→power reduction.
  have hterm : ∀ n ∈ Finset.range (K + 1),
      ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)
        ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ e := by
    intro n _
    have := latticeSphere_card_mul_rpow_le d hd n (-α)
    rwa [show (d : ℝ) - 1 + -α = e from by rw [he_def]; ring] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- Reindex `∑_{range (K+1)} (1+n)^e = ∑_{Ioc 0 (K+1)} m^e`.
  have hreindex : ∑ n ∈ Finset.range (K + 1), (1 + (n : ℝ)) ^ e
      = ∑ m ∈ Finset.Ioc 0 (K + 1), ((m : ℝ)) ^ e := by
    have hIoc : Finset.Ioc 0 (K + 1) = Finset.Ico 1 (K + 2) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, show (1 : ℕ) = 0 + 1 from rfl, ← Finset.map_add_right_Ico 0 (K + 1) 1,
      Finset.sum_map, Finset.range_eq_Ico]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [addRightEmbedding_apply]
    congr 1
    push_cast
    ring
  rw [hreindex]
  -- Head-sum bound at `N = K+1`.
  have hhead := sum_Ioc_zero_nat_rpow_le he (N := K + 1) (by omega)
  have hee : e + 1 = (d : ℝ) - α := by rw [he_def]; ring
  have hNN : ((K : ℝ) + 1 + 1) = (K : ℝ) + 2 := by ring
  rw [hee] at hhead
  have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hhead
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  rw [hNN] at hhead
  exact mul_le_mul_of_nonneg_left hhead h2d_pos.le

/-- **Radial ball z-sum bound** (`α < d`, `d ≥ 1`): the `ℝ≥0∞` sum over the
lattice points `z` with `latticeDistance d x z ≤ K` of `(1+dist)^{−α}` is bounded
by `ENNReal.ofReal (2^d·((K+2)^{d−α}/(d−α)+1))`.

Bridges the shell-index `radial_shell_ball_sum_le` to a z-indexed `ℝ≥0∞` sum (the
form consumed by the convolution region split): the centre-arbitrary shell
reorganization turns the z-sum into `∑_n card·(if n≤K then …)`, every partial sum
of which is `≤ ∑_{n≤K} card·(1+n)^{−α} = ofReal(radial ball bound)`
(via `ENNReal.tsum_le_of_sum_range_le`). -/
theorem tsum_ball_radial_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < (d : ℝ))
    (x : Fin d → ℤ) (K : ℕ) :
    ∑' z : Fin d → ℤ,
        (if IsingModel.latticeDistance d x z ≤ K then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ d * (((K : ℝ) + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1)) := by
  rw [tsum_radial_eq_tsum_shell_center d x
    (fun n => if n ≤ K then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-α)) else 0)]
  -- Rewrite each shell term `card · (if …)` as `if … then ofReal(card·…) else 0`.
  have hkern : ∀ n : ℕ,
      ((latticeSphere d n).card : ℝ≥0∞) *
          (if n ≤ K then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-α)) else 0)
        = (if n ≤ K then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α))
            else 0) := by
    intro n
    by_cases hn : n ≤ K
    · rw [if_pos hn, if_pos hn,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · rw [if_neg hn, if_neg hn, mul_zero]
  simp_rw [hkern]
  refine ENNReal.tsum_le_of_sum_range_le (fun m => ?_)
  -- Bound the partial sum by the full ball shell-sum, then by `ofReal(bound)`.
  have hsub :
      ∑ n ∈ Finset.range m,
          (if n ≤ K then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)) else 0)
        ≤ ∑ n ∈ Finset.range (K + 1),
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset ?_
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]; omega
  refine hsub.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (radial_shell_ball_sum_le hd hα K)

/-- **Radial shell-sum over a tail** (`d < 2α`, `d ≥ 1`): the shell-weighted
`(1+n)^{−2α}` sum over radii `n > K` (here as a finite `Ioc K m` partial sum) is
bounded by `2^d·(K+1)^{d−2α}/(2α−d)`, uniformly in `m`.

Combines `latticeSphere_card_mul_rpow_le` (term-wise, `s=−2α`) with the tail
integral comparison `sum_Ioc_nat_rpow_le` (at `e = d−1−2α < −1`), after reindexing
`∑_{n∈Ioc K m} (1+n)^e = ∑_{j∈Ioc (K+1) (m+1)} j^e`. -/
theorem radial_shell_tail_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα2 : (d : ℝ) < 2 * α)
    (K m : ℕ) :
    ∑ n ∈ Finset.Ioc K m,
        ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))
      ≤ (2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)) := by
  set e : ℝ := (d : ℝ) - 1 - 2 * α with he_def
  have he : e < -1 := by rw [he_def]; linarith
  -- Term-wise card→power reduction.
  have hterm : ∀ n ∈ Finset.Ioc K m,
      ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))
        ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ e := by
    intro n _
    have := latticeSphere_card_mul_rpow_le d hd n (-(2 * α))
    rwa [show (d : ℝ) - 1 + -(2 * α) = e from by rw [he_def]; ring] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- Reindex `∑_{Ioc K m} (1+n)^e = ∑_{Ioc (K+1) (m+1)} j^e`.
  have hreindex : ∑ n ∈ Finset.Ioc K m, (1 + (n : ℝ)) ^ e
      = ∑ j ∈ Finset.Ioc (K + 1) (m + 1), ((j : ℝ)) ^ e := by
    have hIoc : Finset.Ioc (K + 1) (m + 1) = Finset.Ico (K + 2) (m + 2) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have hIoc2 : Finset.Ioc K m = Finset.Ico (K + 1) (m + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, hIoc2, show K + 2 = (K + 1) + 1 from rfl,
      show m + 2 = (m + 1) + 1 from rfl,
      ← Finset.map_add_right_Ico (K + 1) (m + 1) 1, Finset.sum_map]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [addRightEmbedding_apply]
    congr 1
    push_cast
    ring
  rw [hreindex]
  -- Tail integral comparison at `R = K+1`, `M = m+1`.
  by_cases hKm : K + 1 ≤ m + 1
  · have htail := sum_Ioc_nat_rpow_le he (R := K + 1) (M := m + 1) (by omega) hKm
    have hee : -(e + 1) = 2 * α - (d : ℝ) := by rw [he_def]; ring
    have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
    rw [hee, hcast] at htail
    have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    calc (2 : ℝ) ^ d * ∑ j ∈ Finset.Ioc (K + 1) (m + 1), ((j : ℝ)) ^ e
        ≤ (2 : ℝ) ^ d * (((K : ℝ) + 1) ^ (e + 1) / (2 * α - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left htail h2d_pos.le
      _ = (2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)) := by
          rw [show e + 1 = (d : ℝ) - 2 * α from by rw [he_def]; ring]; ring
  · have hempty : Finset.Ioc (K + 1) (m + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, mul_zero]
    apply div_nonneg
    · positivity
    · linarith

/-- **Radial tail z-sum bound** (`d < 2α`, `d ≥ 1`): the `ℝ≥0∞` sum over lattice
points `z` with `K < latticeDistance d x z` of `(1+dist)^{−2α}` is bounded by
`ENNReal.ofReal (2^d·(K+1)^{d−2α}/(2α−d))`.

The far-region engine bridge: centre-arbitrary shell reorganization +
`ENNReal.tsum_le_of_sum_range_le`, each partial sum bounded by `radial_shell_tail_sum_le`. -/
theorem tsum_tail_radial_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα2 : (d : ℝ) < 2 * α)
    (x : Fin d → ℤ) (K : ℕ) :
    ∑' z : Fin d → ℤ,
        (if K < IsingModel.latticeDistance d x z then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-(2 * α))) else 0)
      ≤ ENNReal.ofReal
          ((2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ))) := by
  rw [tsum_radial_eq_tsum_shell_center d x
    (fun n => if K < n then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-(2 * α))) else 0)]
  have hkern : ∀ n : ℕ,
      ((latticeSphere d n).card : ℝ≥0∞) *
          (if K < n then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-(2 * α))) else 0)
        = (if K < n then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α)))
            else 0) := by
    intro n
    by_cases hn : K < n
    · rw [if_pos hn, if_pos hn,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · rw [if_neg hn, if_neg hn, mul_zero]
  simp_rw [hkern]
  refine ENNReal.tsum_le_of_sum_range_le (fun m => ?_)
  have hsub :
      ∑ n ∈ Finset.range m,
          (if K < n then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α)))
            else 0)
        ≤ ∑ n ∈ Finset.Ioc K m,
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset ?_
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_Ioc]; omega
  refine hsub.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (radial_shell_tail_sum_le hd hα2 K m)

/-- **Near-x region bound** of the sharp HLS convolution (`α < d`, `d ≥ 1`): the
sum over `z` with `2·dist(x,z) ≤ D := dist(x,y)` of
`ofReal((1+dist x z)^{−α})·ofReal((1+dist y z)^{−α})` is bounded by
`ofReal((1+K)^{−α}) · ofReal(2^d·((K+2)^{d−α}/(d−α)+1))` with `K := D/2`.

In this region `dist(y,z) ≥ D − dist(x,z) ≥ K` (triangle inequality), so the
`y`-factor is `≤ ofReal((1+K)^{−α})`; factoring it out (`ENNReal.tsum_mul_right`)
leaves the radial ball sum `tsum_ball_radial_le`. -/
theorem tsum_nearx_region_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hαnn : 0 ≤ α) (hα : α < (d : ℝ))
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        (if 2 * IsingModel.latticeDistance d x z ≤ IsingModel.latticeDistance d x y then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((1 + ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((2 : ℝ) ^ d *
            ((((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) + 2) ^ ((d : ℝ) - α) /
              ((d : ℝ) - α) + 1)) := by
  have hα0 : (-α) ≤ 0 := by linarith
  set D := IsingModel.latticeDistance d x y with hD
  set K := D / 2 with hK
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 + (K : ℝ)) ^ (-α)) with hC
  -- Pointwise: near-x term ≤ (ball indicator)·C.
  have hcover : ∀ z : Fin d → ℤ,
      (if 2 * IsingModel.latticeDistance d x z ≤ D then
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
        ≤ (if IsingModel.latticeDistance d x z ≤ K then
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) else 0) * C := by
    intro z
    by_cases hz : 2 * IsingModel.latticeDistance d x z ≤ D
    · rw [if_pos hz, if_pos (by omega : IsingModel.latticeDistance d x z ≤ K)]
      -- y-factor ≤ C.
      have hyge : K ≤ IsingModel.latticeDistance d y z := by
        have htri := IsingModel.latticeDistance_triangle d x z y
        rw [IsingModel.latticeDistance_comm d z y] at htri
        omega
      have hyle : ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) ≤ C := by
        rw [hC]
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hα0
        have : (K : ℝ) ≤ (IsingModel.latticeDistance d y z : ℝ) := by exact_mod_cast hyge
        linarith
      exact mul_le_mul' le_rfl hyle
    · rw [if_neg hz]
      exact zero_le _
  refine (ENNReal.tsum_le_tsum hcover).trans ?_
  rw [ENNReal.tsum_mul_right, mul_comm]
  exact mul_le_mul' le_rfl (tsum_ball_radial_le hd hα x K)

/-- **Far region bound** of the sharp HLS convolution (`d < 2α`, `0 ≤ α`,
`d ≥ 1`): the sum over `z` with `D < 2·dist(x,z)` and `D < 2·dist(y,z)`
(`D := dist(x,y)`) of `ofReal((1+dist x z)^{−α})·ofReal((1+dist y z)^{−α})` is
bounded by `ofReal(3^α) · ofReal(2^d·(K+1)^{d−2α}/(2α−d))` with `K := D/2`.

In this region `dist(x,z) ≤ D + dist(y,z) < 3·dist(y,z)` (triangle + `D<2·dist(y,z)`),
so `1+dist(x,z) ≤ 3(1+dist(y,z))`, hence the product is
`≤ ofReal(3^α)·ofReal((1+dist x z)^{−2α})`; restricting to `K < dist(x,z)` and
applying `tsum_tail_radial_le` closes it. -/
theorem tsum_far_region_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα2 : (d : ℝ) < 2 * α) (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        (if IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d x z ∧
            IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d y z then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((3 : ℝ) ^ α) *
          ENNReal.ofReal ((2 : ℝ) ^ d *
            ((IsingModel.latticeDistance d x y / 2 : ℕ) + 1 : ℝ) ^ ((d : ℝ) - 2 * α) /
              (2 * α - (d : ℝ))) := by
  set D := IsingModel.latticeDistance d x y with hD
  set K := D / 2 with hK
  have hcover : ∀ z : Fin d → ℤ,
      (if D < 2 * IsingModel.latticeDistance d x z ∧
          D < 2 * IsingModel.latticeDistance d y z then
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
        ≤ ENNReal.ofReal ((3 : ℝ) ^ α) *
            (if K < IsingModel.latticeDistance d x z then
              ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-(2 * α)))
              else 0) := by
    intro z
    by_cases hz : D < 2 * IsingModel.latticeDistance d x z ∧
        D < 2 * IsingModel.latticeDistance d y z
    · obtain ⟨hzx, hzy⟩ := hz
      rw [if_pos ⟨hzx, hzy⟩, if_pos (show K < IsingModel.latticeDistance d x z by
        rw [hK]; exact Nat.div_lt_of_lt_mul (by omega))]
      set a : ℝ := 1 + (IsingModel.latticeDistance d x z : ℝ) with ha_def
      set b : ℝ := 1 + (IsingModel.latticeDistance d y z : ℝ) with hb_def
      have ha_pos : 0 < a := by rw [ha_def]; positivity
      have hb_pos : 0 < b := by rw [hb_def]; positivity
      -- comparability `a ≤ 3*b`.
      have hab : a ≤ 3 * b := by
        have htri := IsingModel.latticeDistance_triangle d x y z
        have h1 : (IsingModel.latticeDistance d x z : ℝ)
            ≤ 3 * (IsingModel.latticeDistance d y z : ℝ) := by
          have : IsingModel.latticeDistance d x z ≤ 3 * IsingModel.latticeDistance d y z := by omega
          exact_mod_cast this
        rw [ha_def, hb_def]; linarith
      -- `b^{-α} ≤ 3^α · a^{-α}`.
      have hble : b ^ (-α) ≤ (3 : ℝ) ^ α * a ^ (-α) := by
        have h3b : ((3 : ℝ) * b) ^ (-α) ≤ a ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos ha_pos hab (by linarith)
        rw [Real.mul_rpow (by norm_num) hb_pos.le] at h3b
        have h3 : (3 : ℝ) ^ (-α) = ((3 : ℝ) ^ α)⁻¹ := by
          rw [← Real.rpow_neg (by norm_num)]
        rw [h3] at h3b
        have h3pos : (0 : ℝ) < (3 : ℝ) ^ α := by positivity
        rw [inv_mul_le_iff₀ h3pos] at h3b
        linarith [h3b]
      -- product bound, in ℝ then lifted via ofReal.
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have ha2 : a ^ (-α) * a ^ (-α) = a ^ (-(2 * α)) := by
        rw [← Real.rpow_add ha_pos]; congr 1; ring
      calc a ^ (-α) * b ^ (-α)
          ≤ a ^ (-α) * ((3 : ℝ) ^ α * a ^ (-α)) :=
            mul_le_mul_of_nonneg_left hble (by positivity)
        _ = (3 : ℝ) ^ α * (a ^ (-α) * a ^ (-α)) := by ring
        _ = (3 : ℝ) ^ α * a ^ (-(2 * α)) := by rw [ha2]
    · rw [if_neg hz]
      exact zero_le _
  refine (ENNReal.tsum_le_tsum hcover).trans ?_
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul' le_rfl (tsum_tail_radial_le hd hα2 x K)

/-- **Three-region cover** of the sharp HLS convolution: the full sum is bounded
by the sum of the near-x, near-y and far region sums.

Every `z` lies in at least one region (`2·dist(x,z) ≤ D`, `2·dist(y,z) ≤ D`, or
`D < 2·dist(x,z) ∧ D < 2·dist(y,z)` with `D := dist(x,y)`), and the summand is
nonnegative, so the un-indicatored value is dominated pointwise by the sum of its
three indicator copies; `ENNReal.tsum_le_tsum` + `ENNReal.tsum_add` lift this. -/
theorem tsum_conv_le_sum_regions {d : ℕ} {α : ℝ} (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α))
      ≤ (∑' z : Fin d → ℤ,
            (if 2 * IsingModel.latticeDistance d x z ≤ IsingModel.latticeDistance d x y then
              ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
                ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0))
        + (∑' z : Fin d → ℤ,
            (if 2 * IsingModel.latticeDistance d y z ≤ IsingModel.latticeDistance d x y then
              ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
                ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0))
        + (∑' z : Fin d → ℤ,
            (if IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d x z ∧
                IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d y z then
              ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
                ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun z => ?_)
  set t : ℝ≥0∞ :=
    ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
      ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) with ht
  by_cases h1 : 2 * IsingModel.latticeDistance d x z ≤ IsingModel.latticeDistance d x y
  · rw [if_pos h1]
    exact le_self_add.trans le_self_add
  · by_cases h2 : 2 * IsingModel.latticeDistance d y z ≤ IsingModel.latticeDistance d x y
    · rw [if_neg h1, if_pos h2, zero_add]
      exact le_self_add
    · rw [if_neg h1, if_neg h2, if_pos ⟨by omega, by omega⟩, zero_add, zero_add]

end IsingModel
