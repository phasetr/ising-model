import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.CorrelationIncrementPolyPow
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellDecaySum.SeparationHypothesis
import IsingModel.Concrete.CubicExhaustion
import IsingModel.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cubic-shell decay sum (4/4): geometric and uniform bounds

Structural split (4/4) of `Concrete.LatticeGraphCorrelation.CubicShellDecaySum`.  This child
holds the analytic floor-power → geometric conversion `cf^⌊n/m⌋ ≤ (1/cf) · (cf^{1/m})^n` and
the compositions it enables: the cubic absolute increment in clean geometric
high-temperature form (with the separation hypothesis auto-discharged by the sibling
`...SeparationHypothesis`), the `cf_max` uniformization removing the β-dependence of the
contraction factor, and the fully uniform geometric high-temperature bound.  It builds on
the siblings `...CorrelationIncrementPolyPow` and `...SeparationHypothesis`.  See the
`Concrete.LatticeGraphCorrelation.CubicShellDecaySum` facade module for the full contents
overview.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Floor-power → geometric bound** (Issue #3054, Step A). For `0 < cf < 1`
and `m ≥ 1`, the natural-power `cf^⌊n/m⌋` is bounded above by `(1/cf) · ρ^n`
where `ρ := cf^(1/m)` (real power) — i.e., a clean geometric upper bound with
ratio `ρ < 1`. The floor adjustment costs at most a factor `1/cf`.

Key conversion needed to translate the cubic real-axis increment bound
`cf^⌊(k+1-R)/(r₀+2)⌋` (step-wise geometric in `k`) into the `ratio^k` shape
required by the poly-geometric CE-route bundle constructors. -/
theorem cf_pow_natDiv_le_geometric (cf : ℝ) (hcf_pos : 0 < cf) (hcf_lt_one : cf < 1)
    (m : ℕ) (hm : 0 < m) :
    let ρ := cf ^ ((1 : ℝ) / m)
    0 < ρ ∧ ρ < 1 ∧ ∀ n : ℕ, cf ^ (n / m) ≤ (1 / cf) * ρ ^ n := by
  -- Set ρ := cf^(1/m), M := 1/cf.
  refine ⟨?_, ?_, ?_⟩
  · -- 0 < cf^(1/m)
    exact Real.rpow_pos_of_pos hcf_pos _
  · -- cf^(1/m) < 1
    have hm_pos : (0 : ℝ) < 1 / m := by
      have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    exact Real.rpow_lt_one hcf_pos.le hcf_lt_one hm_pos
  · intro n
    -- Strategy: cf^(n/m : ℕ) = Real.rpow cf (n/m : ℕ : ℝ)
    --        ≤ Real.rpow cf ((n : ℝ)/m - 1) since (n/m : ℕ : ℝ) ≥ (n : ℝ)/m - 1
    --        = cf⁻¹ * Real.rpow cf ((n : ℝ)/m)
    --        = cf⁻¹ * (cf^(1/m))^n
    --        = (1/cf) * ρ^n
    have hm_pos_real : (0 : ℝ) < m := by exact_mod_cast hm
    have h_floor_le : ((n : ℝ) / m - 1) ≤ ((n / m : ℕ) : ℝ) := by
      -- (n/m : ℕ) * m + (n % m) = n, n % m < m, so (n/m : ℕ) * m > n - m, i.e.,
      -- (n/m : ℕ) > n/m - 1 (real).
      have h_div_add : (n / m : ℕ) * m + n % m = n := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod n m
      have h_mod_lt : (n % m : ℕ) < m := Nat.mod_lt n hm
      have h_div_real : ((n / m : ℕ) : ℝ) * m = (n : ℝ) - ((n % m : ℕ) : ℝ) := by
        have hcast : (((n / m : ℕ) * m + n % m : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h_div_add
        push_cast at hcast
        linarith
      have h_mod_lt_real : ((n % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h_mod_lt
      -- Want: (n : ℝ)/m - 1 ≤ ((n / m : ℕ) : ℝ)
      -- Equivalently: ((n : ℝ)/m - 1) * m ≤ ((n / m : ℕ) : ℝ) * m
      -- LHS = (n : ℝ) - m, RHS = (n : ℝ) - (n % m : ℝ) > (n : ℝ) - m. ✓
      have hgoal : ((n : ℝ) / m - 1) * m ≤ ((n / m : ℕ) : ℝ) * m := by
        rw [h_div_real]
        have : ((n : ℝ) / m - 1) * m = (n : ℝ) - m := by field_simp
        rw [this]
        linarith
      exact le_of_mul_le_mul_right hgoal hm_pos_real
    -- Use rpow_natCast to convert nat-power to rpow.
    rw [show cf ^ (n / m) = (cf : ℝ) ^ ((n / m : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    -- Apply rpow monotonicity (decreasing for cf < 1)
    have h_step1 :
        (cf : ℝ) ^ ((n / m : ℕ) : ℝ) ≤ cf ^ ((n : ℝ) / m - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hcf_pos hcf_lt_one.le h_floor_le
    refine h_step1.trans ?_
    -- cf^((n:ℝ)/m - 1) = (1/cf) * cf^((n:ℝ)/m) = (1/cf) * (cf^(1/m))^n
    have h_rhs :
        cf ^ ((n : ℝ) / m - 1) = (1 / cf) * (cf ^ ((1 : ℝ) / m)) ^ n := by
      rw [Real.rpow_sub hcf_pos, Real.rpow_one]
      rw [show ((n : ℝ) / m) = ((1 : ℝ) / m) * n by ring]
      rw [Real.rpow_mul hcf_pos.le]
      rw [Real.rpow_natCast]
      ring
    rw [h_rhs]

/-- **Cubic abs in clean geometric high-temperature form** (Issue #3054, Step
A+B composition). Combines `abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp`
(#3116), `hsep_of_cubicBox_R_succ_le_k` (#3118 — auto-discharges `hsep`), and
`cf_pow_natDiv_le_geometric` (#3119 — floor → geometric) to produce the cubic
real-axis abs increment bound in the clean form

    |c_k − c_{k+1}| ≤ (1/cf) · (2k+3)^d · ρ_R^{k+1−R}

with explicit `ρ_R := cf^{1/(r₀+2)} ∈ (0, 1)`. This is the direct
poly·geometric shape compatible with the `R_inc_seq k := M · (2k+3)^d · ρ_R^k`
input of the (now-removed, PR #4301) canonical-radius-sequence poly-geometric
CE-route wrapper (PR #3104, modulo a constant shift `ρ_R^{1−R}`). The cubic high-temperature
hypothesis automatically discharges `hsep` via the threshold `R + 1 ≤ k`,
removing the only combinatorial side-condition. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_geometric_high_temp (d : ℕ) (hd : 1 ≤ d)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J β : ℝ)
    (hβJ2d : β * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (hcf_pos : 0 < contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀)
    (hα : contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ < 1)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ (1 / contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀) *
          (((2 * k + 3 : ℕ) : ℝ) ^ d *
            (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((1 : ℝ) / (r₀ + 2))) ^ (k + 1 - R)) := by
  -- Step 1: apply the high-temp simplification + auto-discharged hsep.
  have hsep := hsep_of_cubicBox_R_succ_le_k d k R hRk hr hs
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp d hd r₀ hr₀ J β hβJ2d hf hα
      k R (by omega) hrs hr hs hsep hcov_k
  -- Step 2: apply Step A (floor → geometric) to the cf^... factor.
  -- cf_pow_natDiv_le_geometric gives cf^((k+1-R)/(r₀+2)) ≤ (1/cf) · ρ_R^(k+1-R)
  have hm_pos : 0 < r₀ + 2 := by omega
  obtain ⟨_, _, hgeom⟩ :=
    cf_pow_natDiv_le_geometric
      (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀)
      hcf_pos hα (r₀ + 2) hm_pos
  have hcf_step := hgeom (k + 1 - R)
  -- Combine: bound ≤ (2k+3)^d · cf^... ≤ (2k+3)^d · (1/cf) · ρ_R^(k+1-R)
  refine hbound.trans ?_
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hstep : ((2 * k + 3 : ℕ) : ℝ) ^ d *
        contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
          ((1 / contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀) *
            (contractionFactor d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) r₀ ^
              ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R)) :=
    mul_le_mul_of_nonneg_left hcf_step hpoly_nn
  refine hstep.trans ?_
  have hcast : ((r₀ + 2 : ℕ) : ℝ) = ((r₀ : ℝ) + 2) := by push_cast; ring
  rw [hcast]
  ring_nf
  exact le_refl _

/-- **Cubic abs uniformized via `cf_max`** (Issue #3054, Step C). The
high-temperature cubic abs increment bound (#3116) with the per-β contraction
factor `cf(β)` replaced by an upper bound `cf_max < 1` valid over the
high-temperature Icc. This is the shape required for the `h_real_inc` slot of
the poly-geometric CE-route bundle constructors, where `R_inc_seq k` must be
independent of β_re.

Given a uniform upper bound `cf_max < 1` on `contractionFactor d (cubicExhaustion d)
⟨J, 0, β_re⟩ r₀` over the relevant β_re range, the cubic abs increment is
bounded by the β_re-independent sequence
`R_inc_seq k := (2k+3)^d · cf_max^{(k+1-R)/(r₀+2)}`. -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max
    (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J : ℝ)
    (cf_max : ℝ) (hcf_max_lt_one : cf_max < 1)
    {β_re : ℝ} (hβ_re_lt : β_re * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β_re⟩ : IsingParams ℝ))
    (h_cf_max : contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ≤ cf_max)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β_re⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β_re⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d * cf_max ^ ((k + 1 - R) / (r₀ + 2)) := by
  -- Derive the per-β_re bound first.
  have h_cf_lt_one :
      contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ < 1 :=
    lt_of_le_of_lt h_cf_max hcf_max_lt_one
  have hsep := hsep_of_cubicBox_R_succ_le_k d k R hRk hr hs
  have hbound :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_poly_pow_high_temp d hd r₀ hr₀ J β_re hβ_re_lt hf
      h_cf_lt_one k R (by omega) hrs hr hs hsep hcov_k
  -- Bound cf^((k+1-R)/(r₀+2)) ≤ cf_max^((k+1-R)/(r₀+2)) using x ≤ y, both in (0, 1) ⇒ x^p ≤ y^p.
  refine hbound.trans ?_
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have h_cf_nn : (0 : ℝ) ≤ contractionFactor d (cubicExhaustion d)
      (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ :=
    contractionFactor_nonneg d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) hf r₀
  have h_cf_pow_le_max_pow :
      contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ^
          ((k + 1 - R) / (r₀ + 2))
        ≤ cf_max ^ ((k + 1 - R) / (r₀ + 2)) :=
    pow_le_pow_left₀ h_cf_nn h_cf_max _
  exact mul_le_mul_of_nonneg_left h_cf_pow_le_max_pow hpoly_nn

/-- **Cubic abs uniform geometric high-temperature** (Issue #3054, Step A + Step C
composition). Combines `abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max`
(#3122, Step C — uniformizing the per-β contraction factor via `cf_max`) with
`cf_pow_natDiv_le_geometric` (#3119, Step A — floor → geometric conversion) to
produce the fully-simplified bound

    |c_k − c_{k+1}| ≤ (1/cf_max) · (2k+3)^d · ρ_R_max^{k+1−R}

with explicit `ρ_R_max := cf_max^{1/(r₀+2)} ∈ (0, 1)`. β_re-independent
(everything controlled by `cf_max`) and fully geometric in `k` (no nat-floor).
This is the cleanest cubic real-axis abs increment expression compatible with
the `R_inc_seq k` input slot of the poly-geometric CE-route bundle
constructors (PRs #3099-#3105). -/
theorem abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_geometric_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (J : ℝ)
    (cf_max : ℝ) (hcf_max_pos : 0 < cf_max) (hcf_max_lt_one : cf_max < 1)
    {β_re : ℝ} (hβ_re_lt : β_re * J * (2 * d) ≤ 1)
    (hf : Ferromagnetic (⟨J, 0, β_re⟩ : IsingParams ℝ))
    (h_cf_max : contractionFactor d (cubicExhaustion d) (⟨J, 0, β_re⟩ : IsingParams ℝ) r₀ ≤ cf_max)
    (k R : ℕ) (hRk : R + 1 ≤ k)
    {r s : Fin d → ℤ} (hrs : r ≠ s) (hr : r ∈ cubicBox d R) (hs : s ∈ cubicBox d R)
    (hcov_k : ({r, s} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume k) :
    |correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume k))
          (⟨J, 0, β_re⟩ : IsingParams ℝ) (liftFinset {r, s} hcov_k) -
        correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume (k + 1)))
          (⟨J, 0, β_re⟩ : IsingParams ℝ)
          (liftFinset {r, s} (hcov_k.trans ((cubicExhaustion d).mono (Nat.le_succ k))))|
      ≤ (1 / cf_max) * ((2 * k + 3 : ℕ) : ℝ) ^ d *
          (cf_max ^ ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R) := by
  -- Step 1: Step C bound — (2k+3)^d · cf_max^((k+1-R)/(r₀+2))
  have hstep_c :=
    abs_correlation_inducedGraph_cubic_succ_sub_le_uniform_cf_max d hd r₀ hr₀ J cf_max
      hcf_max_lt_one
      hβ_re_lt hf h_cf_max k R hRk hrs hr hs hcov_k
  refine hstep_c.trans ?_
  -- Step 2: Step A on cf_max — cf_max^((k+1-R)/(r₀+2)) ≤ (1/cf_max) · ρ_R_max^(k+1-R)
  have hm_pos : 0 < r₀ + 2 := by omega
  obtain ⟨_, _, hgeom⟩ :=
    cf_pow_natDiv_le_geometric cf_max hcf_max_pos hcf_max_lt_one (r₀ + 2) hm_pos
  have hcf_geom := hgeom (k + 1 - R)
  -- Bound (2k+3)^d · cf_max^((k+1-R)/(r₀+2)) ≤ (2k+3)^d · (1/cf_max) · ρ_R_max^(k+1-R)
  have hpoly_nn : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d := pow_nonneg (by positivity) _
  have hstep : ((2 * k + 3 : ℕ) : ℝ) ^ d * cf_max ^ ((k + 1 - R) / (r₀ + 2))
      ≤ ((2 * k + 3 : ℕ) : ℝ) ^ d *
          ((1 / cf_max) * (cf_max ^ ((1 : ℝ) / ((r₀ + 2 : ℕ) : ℝ))) ^ (k + 1 - R)) :=
    mul_le_mul_of_nonneg_left hcf_geom hpoly_nn
  refine hstep.trans ?_
  ring_nf
  exact le_refl _

end Ambient
end IsingModel
