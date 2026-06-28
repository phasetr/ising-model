import IsingModel.PseudoMass.Profile

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1k: the bounded pseudo-mass denominator ratio (p.312)

A pure arithmetic bound enabling the GJ-faithful **bounded** incident "`2A`" term.  The incident
reduced correlation divided by `c = ⟨φ_x φ_z⟩` is, via the per-incident-dart ratio (#4342),
`(1+(m⁻·r)^α)·(1/(1+(m⁻·s)^α))·e^{m⁻}` with `r = d(x,z)`, `s = d(z,v) ≥ r−1` (`v ∼ x`).
For a *non-adjacent* binding pair (`r ≥ 2`), the ratio `(1+(m⁻r)^α)/(1+(m⁻s)^α)` is bounded by
the **constant** `1 + 2^α` (since `s ≥ r−1 ≥ r/2`, so `r ≤ 2s` and `(m⁻r)^α ≤ 2^α(m⁻s)^α`).  This
is the bounded `2A` of GJ p.312 — the incident term must **not** drop the denominator (leaving the
unbounded `(1+(m⁻r)^α)`); keeping it yields a `dist`-independent constant.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

/-- **Bounded pseudo-mass denominator ratio** (GJ p.312 `2A`): for `0 ≤ m`, `2 ≤ r`, `r−1 ≤ s`,
`(1+(m·r)^α)/(1+(m·s)^α) ≤ 1 + 2^α`.  Since `r ≥ 2` gives `r−1 ≥ r/2`, we have `s ≥ r/2`, i.e.
`r ≤ 2s`, so `(m·r)^α ≤ 2^α·(m·s)^α`; the ratio is then `≤ 1 + 2^α`. -/
theorem pseudoMass_denom_ratio_le {α : ℕ} {m r s : ℝ} (hm : 0 ≤ m) (hr : 2 ≤ r) (hs : r - 1 ≤ s) :
    (1 + (m * r) ^ α) / (1 + (m * s) ^ α) ≤ 1 + 2 ^ α := by
  have hs_nn : 0 ≤ s := by linarith
  have hr2s : r ≤ 2 * s := by linarith
  have hpow_s : (0 : ℝ) ≤ (m * s) ^ α := pow_nonneg (mul_nonneg hm hs_nn) α
  have hden : (0 : ℝ) < 1 + (m * s) ^ α := by linarith
  rw [div_le_iff₀ hden]
  have hmr_le : m * r ≤ 2 * (m * s) := by
    rw [show 2 * (m * s) = m * (2 * s) by ring]
    exact mul_le_mul_of_nonneg_left hr2s hm
  have hkey : (m * r) ^ α ≤ 2 ^ α * (m * s) ^ α := by
    calc (m * r) ^ α ≤ (2 * (m * s)) ^ α :=
          pow_le_pow_left₀ (mul_nonneg hm (by linarith)) hmr_le α
      _ = 2 ^ α * (m * s) ^ α := by rw [mul_pow]
  have h2 : (0 : ℝ) ≤ 2 ^ α := by positivity
  nlinarith [hkey, hpow_s, h2, mul_nonneg h2 hpow_s]

end Ambient
end IsingModel
