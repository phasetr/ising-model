import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Contraction
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.AmbientLattice.TruncatedFunctions.TwoPoint

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

end Ambient
end IsingModel
