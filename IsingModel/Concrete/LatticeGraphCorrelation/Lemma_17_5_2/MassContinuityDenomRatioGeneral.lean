import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDenomRatio

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV4b-adj: the bounded denominator ratio for any `r ≤ 2s`

The adjacency-general version of `pseudoMass_denom_ratio_le` (#4337).  The bounded incident "`2A`"
ratio `(1+(m·r)^α)/(1+(m·s)^α) ≤ 1 + 2^α` holds whenever `r ≤ 2s` (with `0 ≤ m`, `0 ≤ s`) — the
existing lemma's `2 ≤ r` is unnecessarily strong.  This covers the **adjacent** binding pair `r = 1`
(where the incident neighbour `w` of `x` with `z ≠ w` gives `s = d(z,w) ≥ 1`, so `r = 1 ≤ 2 ≤ 2s`),
which the inf' minimiser is generically.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

/-- **Bounded denominator ratio (general `r ≤ 2s`)** (GJ p.312 `2A`): for `0 ≤ m`, `0 ≤ r`, `0 ≤ s`,
`r ≤ 2s`, `(1+(m·r)^α)/(1+(m·s)^α) ≤ 1 + 2^α`.  Same proof as `pseudoMass_denom_ratio_le` (#4337)
but with the weaker, adjacency-compatible hypothesis `r ≤ 2s` directly (the `2 ≤ r`, `r−1 ≤ s` case
gives `r ≤ 2s`; the adjacent `r = 1`, `s ≥ 1` case also gives `r ≤ 2s`). -/
theorem pseudoMass_denom_ratio_le_general {α : ℕ} {m r s : ℝ} (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hr2s : r ≤ 2 * s) :
    (1 + (m * r) ^ α) / (1 + (m * s) ^ α) ≤ 1 + 2 ^ α := by
  have hpow_s : (0 : ℝ) ≤ (m * s) ^ α := pow_nonneg (mul_nonneg hm hs) α
  have hden : (0 : ℝ) < 1 + (m * s) ^ α := by linarith
  rw [div_le_iff₀ hden]
  have hmr_le : m * r ≤ 2 * (m * s) := by
    rw [show 2 * (m * s) = m * (2 * s) by ring]
    exact mul_le_mul_of_nonneg_left hr2s hm
  have hkey : (m * r) ^ α ≤ 2 ^ α * (m * s) ^ α := by
    calc (m * r) ^ α ≤ (2 * (m * s)) ^ α :=
          pow_le_pow_left₀ (mul_nonneg hm hr) hmr_le α
      _ = 2 ^ α * (m * s) ^ α := by rw [mul_pow]
  have h2 : (0 : ℝ) ≤ 2 ^ α := by positivity
  nlinarith [hkey, hpow_s, h2, mul_nonneg h2 hpow_s]

end Ambient
end IsingModel
