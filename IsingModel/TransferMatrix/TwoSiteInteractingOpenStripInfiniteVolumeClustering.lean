import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripInfiniteVolume

/-!
# Exponential clustering and axis summability for the `K2` open strip (GJ §17.1)

This file packages the infinite-volume `K2` (transverse width `2`) open-strip exponential
decay bound `abs_correlationInfinite_stripGraph_axis_le` of
`TwoSiteInteractingOpenStripInfiniteVolume` into the standard *exponential clustering*
consequences: nonnegativity of the spectral prefactor, the geometric ratio
`exp(-mass) < 1`, the vanishing of the axis two-point correlation along the separation,
and the summability of the correlation magnitudes along the strip axis (with explicit
geometric-series majorant).

Writing `m := twoSiteInteractingMass (βJ)` (`> 0` whenever `0 < βJ`) and
`prefactor := k2StripPrefactor p hp x`, the headline bound reads
`|corr sep| ≤ prefactor · exp(-m · sep)` for every `sep ≥ 1`.  Because `exp(-m) < 1`, the
majorant `∑ sep, prefactor · exp(-m · sep)` is a convergent geometric series with sum
`prefactor / (1 - exp(-m))`, which yields directional summability of the correlation
magnitudes and an explicit upper bound on their sum.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- The spectral prefactor of the `K2` open-strip decay bound is nonnegative.  Instantiating
the headline decay at separation `1` gives `0 ≤ |corr 1| ≤ prefactor · exp(-m · 1)`, and
since `exp(-m · 1) > 0`, the prefactor itself is nonnegative. -/
theorem k2StripPrefactor_nonneg (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    0 ≤ k2StripPrefactor p hp x := by
  have hbound : 0 ≤ k2StripPrefactor p hp x
      * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * (1 : ℕ)) :=
    (abs_nonneg _).trans
      (abs_correlationInfinite_stripGraph_axis_le p hp hβJ x 1 one_pos)
  have hexp : 0 < Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * (1 : ℕ)) :=
    Real.exp_pos _
  exact nonneg_of_mul_nonneg_left hbound hexp

/-- The geometric ratio `exp(-mass)` of the `K2` open-strip majorant is `< 1`, since the
strip mass `m = twoSiteInteractingMass (βJ)` is strictly positive (so `-m < 0`). -/
theorem exp_neg_mass_lt_one (p : IsingParams ℝ) (hβJ : 0 < p.β * p.J) :
    Real.exp (-(twoSiteInteractingMass (p.β * p.J))) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr (twoSiteInteractingMass_pos hβJ))

/-- **Axis exponential clustering**: the infinite-volume `K2` open-strip axis two-point
correlation of two same-transverse-site points separated by `sep` tends to `0` as
`sep → ∞`.  By the headline decay it is squeezed (eventually, for `sep ≥ 1`) between `0`
and `prefactor · exp(-m · sep)`, and the latter tends to `0` because `m > 0`. -/
theorem tendsto_correlationInfinite_stripGraph_axis_zero (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    Tendsto
      (fun sep : ℕ =>
        Ambient.correlationInfinite stripGraph stripExhaustion p (stripAxisTwoPoint x sep))
      atTop (𝓝 0) := by
  set m := twoSiteInteractingMass (p.β * p.J) with hm
  -- The majorant tends to `0`: `-m · sep → -∞`, hence `exp → 0`, times a constant.
  have hlin : Tendsto (fun sep : ℕ => -m * (sep : ℝ)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr (twoSiteInteractingMass_pos hβJ))
      tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun sep : ℕ => Real.exp (-m * (sep : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hbound :
      Tendsto (fun sep : ℕ => k2StripPrefactor p hp x * Real.exp (-m * (sep : ℝ)))
        atTop (𝓝 0) := by
    have := hexp.const_mul (k2StripPrefactor p hp x)
    simpa using this
  -- Squeeze the correlation magnitude by the majorant (eventually, for `sep ≥ 1`).
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with sep hsep
  rw [Real.norm_eq_abs]
  exact abs_correlationInfinite_stripGraph_axis_le p hp hβJ x sep hsep

/-- The geometric majorant `sep ↦ prefactor · exp(-m · sep)` of the `K2` open-strip decay
is summable: rewriting `exp(-m · sep) = (exp(-m))^sep` exhibits it as a constant multiple of
the convergent geometric series with ratio `exp(-m) < 1`. -/
theorem summable_k2StripPrefactor_exp_neg_mass (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    Summable
      (fun sep : ℕ =>
        k2StripPrefactor p hp x
          * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep)) := by
  have hrw : (fun sep : ℕ =>
        k2StripPrefactor p hp x
          * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep))
      = fun sep : ℕ =>
        k2StripPrefactor p hp x
          * (Real.exp (-(twoSiteInteractingMass (p.β * p.J)))) ^ sep := by
    funext sep
    rw [mul_comm (-(twoSiteInteractingMass (p.β * p.J))) (sep : ℝ), Real.exp_nat_mul]
  rw [hrw]
  exact
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (exp_neg_mass_lt_one p hβJ)).mul_left _

/-- The total of the geometric majorant is the closed-form geometric sum
`prefactor / (1 - exp(-m))`.  Rewriting `exp(-m · sep) = (exp(-m))^sep` and pulling out the
constant `prefactor` reduces to the geometric series identity `∑ r^n = (1 - r)⁻¹`. -/
theorem tsum_k2StripPrefactor_exp_neg_mass (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    ∑' sep : ℕ,
        k2StripPrefactor p hp x
          * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep)
      = k2StripPrefactor p hp x
          / (1 - Real.exp (-(twoSiteInteractingMass (p.β * p.J)))) := by
  have hrw : (fun sep : ℕ =>
        k2StripPrefactor p hp x
          * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep))
      = fun sep : ℕ =>
        k2StripPrefactor p hp x
          * (Real.exp (-(twoSiteInteractingMass (p.β * p.J)))) ^ sep := by
    funext sep
    rw [mul_comm (-(twoSiteInteractingMass (p.β * p.J))) (sep : ℝ), Real.exp_nat_mul]
  rw [hrw, tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mass_lt_one p hβJ),
    div_eq_mul_inv]

/-- **Axis directional summability**: the magnitudes of the infinite-volume `K2`
open-strip axis two-point correlations are summable over the separation `sep`.  The `sep ≥ 1`
terms are dominated by the summable geometric majorant `prefactor · exp(-m · sep)`
(via `summable_nat_add_iff`, shifting back the single `sep = 0` term). -/
theorem summable_abs_correlationInfinite_stripGraph_axis (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    Summable
      (fun sep : ℕ =>
        |Ambient.correlationInfinite stripGraph stripExhaustion p
          (stripAxisTwoPoint x sep)|) := by
  -- It suffices to prove summability of the shifted family `sep ↦ |corr (sep + 1)|`.
  rw [← summable_nat_add_iff 1]
  -- The shifted majorant `sep ↦ prefactor · exp(-m · (sep + 1))` is summable.
  have hmaj :
      Summable
        (fun sep : ℕ =>
          k2StripPrefactor p hp x
            * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * ((sep : ℝ) + 1))) := by
    have hfull := summable_k2StripPrefactor_exp_neg_mass p hp hβJ x
    rw [← summable_nat_add_iff 1] at hfull
    convert hfull using 2 with sep
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun sep => ?_) hmaj
  have hbd := abs_correlationInfinite_stripGraph_axis_le p hp hβJ x (sep + 1)
    (Nat.succ_pos _)
  rw [show ((sep + 1 : ℕ) : ℝ) = (sep : ℝ) + 1 by push_cast; ring] at hbd
  exact hbd

/-- **Axis summed-magnitude bound**: the total of the magnitudes of the infinite-volume
`K2` open-strip axis two-point correlations is bounded by the `sep = 0` term plus the
closed-form geometric sum `prefactor / (1 - exp(-m))`.  Splitting off the `sep = 0` term and
dominating each `sep ≥ 1` magnitude by
`prefactor · exp(-m · (sep + 1)) ≤ prefactor · exp(-m · sep)`
(using `prefactor ≥ 0` and `exp(-m · (sep + 1)) ≤ exp(-m · sep)`) yields the geometric sum. -/
theorem tsum_abs_correlationInfinite_stripGraph_axis_le (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x : Fin 2) :
    ∑' sep : ℕ,
        |Ambient.correlationInfinite stripGraph stripExhaustion p
          (stripAxisTwoPoint x sep)|
      ≤ |Ambient.correlationInfinite stripGraph stripExhaustion p
            (stripAxisTwoPoint x 0)|
        + k2StripPrefactor p hp x
            / (1 - Real.exp (-(twoSiteInteractingMass (p.β * p.J)))) := by
  set m := twoSiteInteractingMass (p.β * p.J) with hm
  have hpref : 0 ≤ k2StripPrefactor p hp x := k2StripPrefactor_nonneg p hp hβJ x
  -- Split off the `sep = 0` term.
  rw [(summable_abs_correlationInfinite_stripGraph_axis p hp hβJ x).tsum_eq_zero_add]
  -- Reduce to bounding the shifted tail by the geometric sum.
  have hgoal :
      ∑' sep : ℕ,
          |Ambient.correlationInfinite stripGraph stripExhaustion p
            (stripAxisTwoPoint x (sep + 1))|
        ≤ k2StripPrefactor p hp x / (1 - Real.exp (-m)) := by
    -- The full geometric majorant is summable, and so is the shifted one.
    have hsumFull := summable_k2StripPrefactor_exp_neg_mass p hp hβJ x
    have hsumShift :
        Summable
          (fun sep : ℕ => k2StripPrefactor p hp x * Real.exp (-m * (sep + 1))) := by
      have := hsumFull
      rw [← summable_nat_add_iff 1] at this
      simpa using this
    have hsumTail :
        Summable
          (fun sep : ℕ =>
            |Ambient.correlationInfinite stripGraph stripExhaustion p
              (stripAxisTwoPoint x (sep + 1))|) := by
      have := summable_abs_correlationInfinite_stripGraph_axis p hp hβJ x
      rw [← summable_nat_add_iff 1] at this
      simpa using this
    -- Termwise: `|corr (sep+1)| ≤ prefactor·exp(-m·(sep+1)) ≤ prefactor·exp(-m·sep)`.
    calc
      ∑' sep : ℕ,
          |Ambient.correlationInfinite stripGraph stripExhaustion p
            (stripAxisTwoPoint x (sep + 1))|
          ≤ ∑' sep : ℕ, k2StripPrefactor p hp x * Real.exp (-m * (sep + 1)) := by
            refine hsumTail.tsum_le_tsum (fun sep => ?_) hsumShift
            have := abs_correlationInfinite_stripGraph_axis_le p hp hβJ x (sep + 1)
              (Nat.succ_pos _)
            simpa using this
      _ ≤ ∑' sep : ℕ, k2StripPrefactor p hp x * Real.exp (-m * sep) := by
            refine hsumShift.tsum_le_tsum (fun sep => ?_) hsumFull
            have hle : Real.exp (-m * (sep + 1)) ≤ Real.exp (-m * sep) := by
              rw [Real.exp_le_exp]
              have hmpos : 0 < m := twoSiteInteractingMass_pos hβJ
              have : -m * ((sep : ℝ) + 1) ≤ -m * sep := by nlinarith
              simpa using this
            exact mul_le_mul_of_nonneg_left hle hpref
      _ = k2StripPrefactor p hp x / (1 - Real.exp (-m)) :=
            tsum_k2StripPrefactor_exp_neg_mass p hp hβJ x
  gcongr

end TransferMatrix

end IsingModel
