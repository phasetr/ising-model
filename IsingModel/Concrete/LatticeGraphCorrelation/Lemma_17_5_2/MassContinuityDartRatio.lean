import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityRatioBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDartScaledHLS

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1c: dart-level exp-cancellation and per-dart correlation ratio

Building blocks of the GJ p.312 derivative-ratio bound for the Ising β-derivative (whose Lebowitz
numerator is a nearest-neighbour edge/dart cross-sum).  This file provides:

* `exp_neg_scaled_dart_pair_le_exp` — the edge analog of `exp_neg_scaled_dist_pair_le_one` (#4329):
  for an adjacent pair `u ∼ v`, `exp(−t·(d(x,u)+d(y,v)−d(x,y))) ≤ exp t` (triangle, edge length 1);
* `pseudoMassG_ratio_le` — the profile-ratio algebra: with `P(r) = pseudoMassG α r m`,
  `P(a)·P(b)/P(c) = 2·(1+(mc)^α)·s_a·s_b·e^{−m(a+b−c)} ≤ 2·(1+(mc)^α)·s_a·s_b·e^{m}` for
  `m,a,b,c ≥ 0` (`s_r = 1/(1+(mr)^α)`), given the exp bound.  Combined with the system-mass majorant
  and the pseudo-mass identity (#4335) and the dart scaled convolution (#4336), this gives the GJ
  p.312 per-dart correlation ratio and the dart-sum/`c` bound (the subject of PR-1d).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Dart-level exp-cancellation.**  For `t ≥ 0` and `v` adjacent to `u`,
`exp(−t·(d(x,u)+d(y,v)−d(x,y))) ≤ exp t`.  The triangle inequality through the edge `{u,v}`
(`d(x,y) ≤ d(x,u)+1+d(y,v)`) gives `d(x,u)+d(y,v)−d(x,y) ≥ −1`, so the exponent is `≤ t`. -/
theorem exp_neg_scaled_dart_pair_le_exp {d : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x y u v : Fin d → ℤ) (hadj : (IsingModel.latticeGraph d).Adj u v) :
    Real.exp (-(t * ((latticeDistance d x u : ℝ) + (latticeDistance d y v : ℝ)
        - (latticeDistance d x y : ℝ)))) ≤ Real.exp t := by
  apply Real.exp_le_exp.mpr
  have huv : latticeDistance d u v = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d u v).mp hadj
  -- d(x,y) ≤ d(x,u) + d(u,y) ≤ d(x,u) + (d(u,v) + d(v,y)) = d(x,u) + 1 + d(y,v).
  have htri1 : latticeDistance d x y ≤ latticeDistance d x u + latticeDistance d u y :=
    latticeDistance_triangle d x u y
  have htri2 : latticeDistance d u y ≤ latticeDistance d u v + latticeDistance d v y :=
    latticeDistance_triangle d u v y
  have hvy : latticeDistance d v y = latticeDistance d y v := latticeDistance_comm d v y
  have hxy_le : (latticeDistance d x y : ℝ)
      ≤ (latticeDistance d x u : ℝ) + 1 + (latticeDistance d y v : ℝ) := by
    have : latticeDistance d x y
        ≤ latticeDistance d x u + 1 + latticeDistance d y v := by
      rw [huv, hvy] at htri2; omega
    exact_mod_cast this
  have hge : (latticeDistance d x u : ℝ) + (latticeDistance d y v : ℝ)
      - (latticeDistance d x y : ℝ) ≥ -1 := by linarith
  nlinarith [ht, hge]

/-- **`pseudoMassG` profile ratio algebra.**  With
`P(r) = pseudoMassG α r m = 2 e^{−mr}/(1+(mr)^α)`,
`P(a)·P(b)/P(c) = 2·(1+(mc)^α)·(1/(1+(ma)^α))·(1/(1+(mb)^α))·e^{−m(a+b−c)}`, which is therefore
`≤ 2·(1+(mc)^α)·(1/(1+(ma)^α))·(1/(1+(mb)^α))·e^{m}` whenever `e^{−m(a+b−c)} ≤ e^{m}` (the dart
exp-cancellation).  This is the pure arithmetic core of the GJ p.312 per-dart ratio. -/
theorem pseudoMassG_ratio_le {α : ℕ} {m a b c : ℝ}
    (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hexp : Real.exp (-(m * (a + b - c))) ≤ Real.exp m) :
    pseudoMassG α a m * pseudoMassG α b m / pseudoMassG α c m
      ≤ 2 * (1 + (m * c) ^ α) * (1 / (1 + (m * a) ^ α)) * (1 / (1 + (m * b) ^ α))
          * Real.exp m := by
  have hda : (0 : ℝ) < 1 + (m * a) ^ α := by positivity
  have hdb : (0 : ℝ) < 1 + (m * b) ^ α := by positivity
  have hdc : (0 : ℝ) < 1 + (m * c) ^ α := by positivity
  have hkey : pseudoMassG α a m * pseudoMassG α b m / pseudoMassG α c m
      = 2 * (1 + (m * c) ^ α) * (1 / (1 + (m * a) ^ α)) * (1 / (1 + (m * b) ^ α))
          * Real.exp (-(m * (a + b - c))) := by
    unfold pseudoMassG
    rw [show -(m * (a + b - c)) = -(m * a) + -(m * b) - -(m * c) by ring,
      Real.exp_sub, Real.exp_add]
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

end Ambient
end IsingModel
