import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.AmbientLattice.TruncatedFunctions.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.SimonLiebDistanceDecay

/-!
# GJ §17.5 / §17.8 — unconditional high-temperature mass gap on `ℤ^d`

The explicit ball-boundary distance decay
`correlationInfinite_latticeGraph_le_explicit_pow_dist` upgrades, at `h = 0`, to
the named `HasExponentialDecay` predicate with an explicit *positive* rate, in
the strong high-temperature regime `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1` with
`β, J > 0` — that is, a positive mass gap holds unconditionally (no
polynomial-decay hypothesis; the underlying ball-boundary shell-contraction axiom
`shellSup_contraction` is still used).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, §17.8 (Theorem 17.8.1),
  pp. 311--318.
-/

namespace IsingModel
namespace Ambient

/-- **Unconditional high-temperature mass gap**: for `β, J > 0` and the explicit
condition `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the infinite-volume Ising model
on `ℤ^d` at `h = 0` has `HasExponentialDecay` with the positive rate
`-log(H)/(r+2)`.

At `h = 0` the Ursell two-point function equals the correlation
(`truncated2Infinite_h_zero`), which the explicit ball-boundary decay
(`correlationInfinite_latticeGraph_le_explicit_pow_dist`) bounds by
`H^{⌊dist/(r+2)⌋} ≤ (1/H)·exp(-(-log H/(r+2))·dist)`; the witness constant is
`C = 1/H`.  No polynomial-decay hypothesis is assumed (the ball-boundary
shell-contraction axiom is still used).  Part of Issue #2931, Phase 3a. -/
theorem hasExponentialDecay_latticeGraph_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (-Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
        (r + 2 : ℝ)) := by
  set H := β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) with hHdef
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
  have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
  have hH_pos : 0 < H := by rw [hHdef]; exact mul_pos hβJ_pos (by positivity)
  have hr2_pos : (0 : ℝ) < (r + 2 : ℝ) := by positivity
  have hlogH_neg : Real.log H < 0 := Real.log_neg hH_pos hht
  set rate := -Real.log H / (r + 2 : ℝ) with hrate
  have hrate_pos : 0 < rate := by rw [hrate]; exact div_pos (by linarith) hr2_pos
  refine ⟨1 / H, by positivity, fun i j hij => ?_⟩
  have htr : truncated2Infinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
    truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β i j
  rw [htr]
  have hcorr_nn := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {i, j}
  rw [abs_of_nonneg hcorr_nn]
  have hdecay :=
    correlationInfinite_latticeGraph_le_explicit_pow_dist d hd r Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hf rfl hht hij
  set n := IsingModel.latticeDistance d i j with hn
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
  have hstep : H ^ (n / (r + 2)) ≤ (1 / H) * Real.exp (-rate * (n : ℝ)) := by
    have h1 : H ^ (n / (r + 2)) ≤ H ^ ((n : ℝ) / (r + 2 : ℝ) - 1) := by
      rw [← Real.rpow_natCast H (n / (r + 2))]
      exact Real.rpow_le_rpow_of_exponent_ge hH_pos hht.le hq_real
    have h2 : H ^ ((n : ℝ) / (r + 2 : ℝ) - 1) = (1 / H) * Real.exp (-rate * (n : ℝ)) := by
      rw [Real.rpow_sub hH_pos, Real.rpow_one, Real.rpow_def_of_pos hH_pos,
        one_div, div_eq_mul_inv, mul_comm (H⁻¹) (Real.exp (-rate * (n : ℝ)))]
      congr 1
      congr 1
      rw [hrate]; ring
    exact h1.trans_eq h2
  calc correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ H ^ (n / (r + 2)) := hdecay
    _ ≤ (1 / H) * Real.exp (-rate * (n : ℝ)) := hstep

/-- **Positivity of the high-temperature decay rate**: for `β, J > 0` and
`H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the mass-gap rate `-log(H)/(r+2)` is
strictly positive. -/
private theorem highTemp_rate_pos
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    0 < -Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
        (r + 2 : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpow_pos : (0 : ℝ) < (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ) := by
    have : 0 < (2 * (r + 1) + 1) ^ d := pow_pos (by omega) d
    exact_mod_cast this
  have hH_pos : 0 < β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) :=
    mul_pos (mul_pos hβ_pos hJ_pos)
      (mul_pos (by norm_num) (mul_pos hd_pos hpow_pos))
  have hlogH_neg : Real.log (β * J * (2 * ((d : ℝ) *
      (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) < 0 := Real.log_neg hH_pos hht
  exact div_pos (by linarith) (by positivity)

/-- **Explicit unconditional high-temperature lower bound on `latticeMass`**: for
`β, J > 0` and `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the lattice mass dominates
the mass-gap rate, `ENNReal.ofReal (-log(H)/(r+2)) ≤ latticeMass d Λ ⟨J,0,β⟩`.

This connects the ball-boundary mass gap (`hasExponentialDecay_latticeGraph_of_high_temp`)
to the supremum definition of `latticeMass` (the central quantity of Lemma 17.5.2)
via `latticeMass_ge_of_HasExponentialDecay`, with no polynomial-decay hypothesis.
Part of Issue #2931, Phase 3a. -/
theorem latticeMass_ge_explicit_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ENNReal.ofReal
        (-Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
          (r + 2 : ℝ))
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (highTemp_rate_pos d hd r hJ_pos hβ_pos hht).le
    (hasExponentialDecay_latticeGraph_of_high_temp d hd r Λ hJ_pos hβ_pos hht)

/-- **Positive lattice mass at strong high temperature, unconditionally**: for
`β, J > 0` and `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`,
`0 < latticeMass d Λ ⟨J,0,β⟩`, from the positive mass-gap rate and
`latticeMass_pos_of_HasExponentialDecay` (no polynomial-decay hypothesis).  Part
of Issue #2931, Phase 3a. -/
theorem latticeMass_pos_of_high_temp_mass_gap
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (Λ : Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay
    (highTemp_rate_pos d hd r hJ_pos hβ_pos hht)
    (hasExponentialDecay_latticeGraph_of_high_temp d hd r Λ hJ_pos hβ_pos hht)

/-- **Unconditional high-temperature convolution summability of the two-point
function**: for `β, J > 0` and `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, the
boundary-product kernel `z ↦ ⟨σ_xσ_z⟩^∞ · ⟨σ_yσ_z⟩^∞` (Ursell two-point at
`h = 0`) is summable over `ℤ^d` for the cubic exhaustion.

This composes the unconditional high-temperature mass gap
(`hasExponentialDecay_latticeGraph_of_high_temp`) with the exponential-decay
convolution summability `summable_truncated2Infinite_prod_of_hasExponentialDecay`
(GJ §17.5 Step 127), with no polynomial-decay hypothesis.  It is the
boundary-sum summability ingredient for the finite-volume → infinite-volume
convergence-rate coupling (Issue #2965, Phase B). -/
theorem summable_truncated2Infinite_prod_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1)
    (x y : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z *
        truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) y z) :=
  summable_truncated2Infinite_prod_of_hasExponentialDecay hJ_pos.le hβ_pos
    (highTemp_rate_pos d hd r hJ_pos hβ_pos hht)
    (hasExponentialDecay_latticeGraph_of_high_temp d hd r (cubicExhaustion d)
      hJ_pos hβ_pos hht)
    x y

/-- **Unconditional high-temperature exponential decay of the two-point
convolution**: for `β, J > 0` and `H := βJ · 2 · (d · (2(r+1)+1)^d) < 1`, there is
a finite constant `C ≥ 0` with
`∑_z ⟨σ_xσ_z⟩^∞ · ⟨σ_yσ_z⟩^∞ ≤ C · exp(-(rate/2)·dist(x,y)/2)` for all `x, y`,
where `rate = -log(H)/(r+2)`.

This composes the unconditional mass gap with the GJ §17.5 Step 127 quantitative
convolution bound `tsum_truncated2Infinite_prod_le`: the boundary convolution
itself decays exponentially in `dist(x,y)`, with no polynomial-decay hypothesis.
The constant `C = (C'+1)^2 · 2·∑_z exp(-(rate/2)·dist(0,z))` absorbs the finite
single-site exponential sum.  Part of Issue #2965, Phase B. -/
theorem tsum_truncated2Infinite_prod_decay_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Fin d → ℤ,
      (∑' z : Fin d → ℤ,
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z *
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) y z)
        ≤ C * Real.exp (-(
            (-Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
              (r + 2 : ℝ)) / 2) * (IsingModel.latticeDistance d x y : ℝ) / 2) := by
  set rate := -Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
    (r + 2 : ℝ) with hrate
  have hrate_pos : 0 < rate := highTemp_rate_pos d hd r hJ_pos hβ_pos hht
  obtain ⟨C', hC', hbound⟩ :=
    hasExponentialDecay_latticeGraph_of_high_temp d hd r (cubicExhaustion d)
      hJ_pos hβ_pos hht
  refine ⟨(C' + 1) ^ 2 *
      (2 * ∑' z : Fin d → ℤ, Real.exp (-(rate / 2) * (IsingModel.latticeDistance d 0 z : ℝ))),
    ?_, fun x y => ?_⟩
  · have hsum_nn : 0 ≤ ∑' z : Fin d → ℤ,
        Real.exp (-(rate / 2) * (IsingModel.latticeDistance d 0 z : ℝ)) :=
      tsum_nonneg (fun z => (Real.exp_pos _).le)
    have : 0 ≤ (C' + 1) ^ 2 := sq_nonneg _
    nlinarith [hsum_nn, this]
  · exact tsum_truncated2Infinite_prod_le hJ_pos.le hβ_pos hrate_pos hC' hbound x y

/-- **Boundary partial-sum exponential decay**: for `β, J > 0` and `H < 1`, the
two-point convolution restricted to **any** finite vertex set `S` is bounded by
the same exponential decay in `dist(x,y)`:
`∑_{b ∈ S} ⟨σ_xσ_b⟩^∞ · ⟨σ_yσ_b⟩^∞ ≤ C · exp(-(rate/2)·dist(x,y)/2)`.

The summands are nonnegative, so the finite partial sum is bounded by the full
`tsum` (`Summable.sum_le_tsum`), which decays by
`tsum_truncated2Infinite_prod_decay_of_high_temp`.  This is the boundary-sum
estimate (uniform over the choice of separating surface `S`) needed for the
finite-volume → infinite-volume convergence-rate coupling (Issue #2965, Phase
A/B). -/
theorem truncated2Infinite_prod_finset_sum_decay_of_high_temp
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ))) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : Fin d → ℤ) (S : Finset (Fin d → ℤ)),
      (∑ b ∈ S,
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x b *
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) y b)
        ≤ C * Real.exp (-(
            (-Real.log (β * J * (2 * ((d : ℝ) * (((2 * (r + 1) + 1) ^ d : ℕ) : ℝ)))) /
              (r + 2 : ℝ)) / 2) * (IsingModel.latticeDistance d x y : ℝ) / 2) := by
  obtain ⟨C, hC, hdecay⟩ :=
    tsum_truncated2Infinite_prod_decay_of_high_temp d hd r hJ_pos hβ_pos hht
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
  refine ⟨C, hC, fun x y S => ?_⟩
  have hsum := summable_truncated2Infinite_prod_of_high_temp d hd r hJ_pos hβ_pos hht x y
  have hpartial :
      (∑ b ∈ S,
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x b *
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) y b)
        ≤ ∑' b : Fin d → ℤ,
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x b *
          truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) y b :=
    hsum.sum_le_tsum S
      (fun b _ => mul_nonneg
        (Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d)
          (cubicExhaustion d) _ hf x b)
        (Ambient.truncated2Infinite_nonneg (IsingModel.latticeGraph d)
          (cubicExhaustion d) _ hf y b))
  exact hpartial.trans (hdecay x y)

/-- **Axiom-free high-temperature exponential decay on `ℤ^d` from `βJ·2d < 1`**: in the
elementary high-temperature regime `0 < βJ·2d < 1` (with `d ≥ 1`), the infinite-volume
two-point truncated function over the cubic exhaustion decays exponentially with rate
`−log(βJ·2d) > 0`:
`HasExponentialDecay d (cubicExhaustion d) ⟨J,0,β⟩ (−log(βJ·2d))`.

Uses only the iterated naive Simon–Lieb peeling bound
`correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt`
(`⟨σ_iσ_j⟩^∞ ≤ (βJ·2d)^{dist−1}`) — no ball-boundary shell-contraction axiom — together
with `truncated2Infinite_h_zero` (at `h=0` the truncated function is the bare correlation)
and `correlationInfinite_nonneg`. Rewriting `(βJ·2d)^{dist−1} = (1/βJ·2d)·exp(log(βJ·2d)·dist)`
gives the constant `C = 1/(βJ·2d)` and rate `−log(βJ·2d)`. This is a cleaner, weaker
high-temperature condition than the shell-based `hasExponentialDecay_latticeGraph_of_high_temp`
(no `(2(r+1)+1)^d` boundary factor, no axiom). -/
theorem hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one
    (d : ℕ) (hd : 1 ≤ d) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * d) < 1) :
    0 < -Real.log (β * J * (2 * d)) ∧
      HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (β * J * (2 * d))) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ_pos.le, le_refl 0, hβ_pos⟩
  have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
  have hB_pos : 0 < β * J * (2 * d) := mul_pos hβJ_pos (by positivity)
  refine ⟨neg_pos.mpr (Real.log_neg hB_pos hht), 1 / (β * J * (2 * d)),
    by positivity, fun i j hij => ?_⟩
  have htr : truncated2Infinite (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
    truncated2Infinite_h_zero (IsingModel.latticeGraph d) (cubicExhaustion d) J β i j
  rw [htr, abs_of_nonneg (correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf {i, j})]
  set n := IsingModel.latticeDistance d i j with hn
  have hn1 : 1 ≤ n :=
    Nat.pos_of_ne_zero (fun h => hij ((latticeDistance_eq_zero_iff d i j).mp h))
  have hdecay := correlationInfinite_latticeGraph_le_betaJ_two_d_pow_of_dist_gt
    (d := d) hβJ_pos.le (n - 1) i j (by omega)
  have hBn : (β * J * (2 * d)) ^ n
      = (β * J * (2 * d)) ^ (n - 1) * (β * J * (2 * d)) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hexp : (β * J * (2 * d)) ^ n
      = Real.exp (-(-Real.log (β * J * (2 * d))) * (n : ℝ)) := by
    rw [neg_neg, ← Real.rpow_natCast (β * J * (2 * d)) n, Real.rpow_def_of_pos hB_pos]
  have heq : (β * J * (2 * d)) ^ (n - 1)
      = 1 / (β * J * (2 * d)) * Real.exp (-(-Real.log (β * J * (2 * d))) * (n : ℝ)) := by
    rw [← hexp, hBn]; field_simp
  exact hdecay.trans_eq heq

/-- **Axiom-free `latticeMass` lower bound under `βJ·2d < 1`**: composing the axiom-free
exponential decay `hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one` with
`latticeMass_ge_of_HasExponentialDecay` gives, for `β, J > 0`, `d ≥ 1`, and
`βJ·2d < 1`,
`ENNReal.ofReal (−log(βJ·2d)) ≤ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩`.
This bounds the central GJ §17.5 Lemma 17.5.2 correlation-length quantity from below by
the explicit elementary high-temperature rate, with no ball-boundary shell-contraction
axiom and no `(2(r+1)+1)^d` boundary factor. -/
theorem latticeMass_ge_of_betaJ_two_d_lt_one
    (d : ℕ) (hd : 1 ≤ d) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * (2 * d)))
      ≤ latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  obtain ⟨hrate_pos, hdecay⟩ :=
    hasExponentialDecay_latticeGraph_of_betaJ_two_d_lt_one d hd hJ_pos hβ_pos hht
  exact latticeMass_ge_of_HasExponentialDecay hrate_pos.le hdecay

/-- **Axiom-free positive `latticeMass` (mass gap) under `βJ·2d < 1`**: since the rate
`−log(βJ·2d)` is strictly positive in the elementary high-temperature regime
`βJ·2d < 1`, the lower bound `latticeMass_ge_of_betaJ_two_d_lt_one` gives a strictly
positive lattice mass `0 < latticeMass d (cubicExhaustion d) ⟨J,0,β⟩` — an axiom-free
positive correlation-length / mass gap. -/
theorem latticeMass_pos_of_betaJ_two_d_lt_one
    (d : ℕ) (hd : 1 ≤ d) {J β : ℝ} (hJ_pos : 0 < J) (hβ_pos : 0 < β)
    (hht : β * J * (2 * d) < 1) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  have hβJ_pos : 0 < β * J := mul_pos hβ_pos hJ_pos
  have hB_pos : 0 < β * J * (2 * d) := mul_pos hβJ_pos (by positivity)
  have hrate_pos : 0 < -Real.log (β * J * (2 * d)) :=
    neg_pos.mpr (Real.log_neg hB_pos hht)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hrate_pos)
    (latticeMass_ge_of_betaJ_two_d_lt_one d hd hJ_pos hβ_pos hht)

end Ambient
end IsingModel
