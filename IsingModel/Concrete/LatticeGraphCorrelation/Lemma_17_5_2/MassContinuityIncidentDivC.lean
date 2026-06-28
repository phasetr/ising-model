import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentRatio
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicIncidentInfiniteBridge

/-!
# GJ §17.5 Theorem 17.5.1 — PR-1g: the per-edge incident `/c` uniform bound (p.312)

The c-cancelling incident error (#4340/#4341) reduces, for an incident edge of the induced cubic
graph and a non-adjacent binding pair `x, z`, to a *single* infinite-volume two-point function
`⟨φ_z φ_w⟩` (`w ∼ x`) or `⟨φ_x φ_w⟩` (`w ∼ z`).  Dividing by `c = ⟨φ_x φ_z⟩` and using the
per-incident-dart ratio (#4342), the `/c` ratio is bounded *uniformly over all incident edges* by
`(1+(m⁻·d(x,z))^α)·e^{m⁻}` — the GJ p.312 bounded `2A` constant.  (The 4-term over-approximation
in `incident_symmDiff_corr_fin_le_infinite` (#4341) is too loose for `/c`: a short-distance factor
like `⟨φ_x φ_w⟩` with `d(x,w)=1` over the exponentially small `c` would blow up; here we keep the
*tight* single-term reduction.)

This module supplies:

* `pseudoMassFromParamsAtPairDist_comm` — symmetry of the per-pair distance pseudo-mass;
* `incident_symmDiff_corr_fin_div_c_le` — the per-edge incident `/c` uniform bound.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **`pseudoMassExt` depends on the radius only through its value**: equal radii give equal
extended pseudo-masses (the radius hypothesis is propositional). -/
theorem pseudoMassExt_congr_r {α : ℕ} (hα : 1 ≤ α) {r₁ r₂ : ℝ} (hr : r₁ = r₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (c : ℝ) :
    pseudoMassExt hα hr₁ c = pseudoMassExt hα hr₂ c := by
  subst hr; rfl

/-- **Symmetry of the per-pair distance pseudo-mass** `m⁻(x,z) = m⁻(z,x)`: the correlation
`⟨φ_x φ_z⟩` and the lattice distance `d(x,z)` are both symmetric, so the distance-parametrized
per-pair pseudo-mass is symmetric. -/
theorem pseudoMassFromParamsAtPairDist_comm {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPairDist hα Λ p x z = pseudoMassFromParamsAtPairDist hα Λ p z x := by
  by_cases h : x = z
  · subst h; rfl
  · have hpos_xz : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun hh => h ((IsingModel.latticeDistance_eq_zero_iff d x z).mp hh))
    have hpos_zx : (0 : ℝ) < (IsingModel.latticeDistance d z x : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun hh => (Ne.symm h) ((IsingModel.latticeDistance_eq_zero_iff d z x).mp hh))
    rw [pseudoMassFromParamsAtPairDist_of_ne hα Λ p h hpos_xz,
      pseudoMassFromParamsAtPairDist_of_ne hα Λ p (Ne.symm h) hpos_zx,
      show ({z, x} : Finset (Fin d → ℤ)) = {x, z} from Finset.pair_comm z x]
    exact pseudoMassExt_congr_r hα
      (by rw [IsingModel.latticeDistance_comm d x z]) hpos_xz hpos_zx _

/-- **Per-edge incident `/c` uniform bound** (GJ p.312, large separation): for a non-adjacent
binding pair `x ≠ z` (`m⁻(x,z) = globalPseudoMassDist`) and an incident edge `{u,v}` of the induced
cubic graph, the c-cancelling reduced incident correlation divided by `c = ⟨φ_x φ_z⟩` is bounded —
uniformly over all incident edges — by `(1+(m⁻·d(x,z))^α)·e^{m⁻}`:
`corr_fin({⟨x⟩,⟨z⟩}△{u,v}) / ⟨φ_x φ_z⟩ ≤ (1+(m⁻·d(x,z))^α)·e^{m⁻}`.

Non-adjacency ⇒ exactly one of `⟨x⟩,⟨z⟩` lies in `{u,v}` (4 cases), so the symmetric difference is a
single two-point set, dominated by its infinite-volume value
(`correlation_inducedGraph_cubic_le_correlationInfinite`); dividing by `c` and applying the
per-incident-dart ratio (#4342 `correlationInfinite_incident_ratio_le`, with the binding-pair
symmetry `pseudoMassFromParamsAtPairDist_comm` for the `z`-incident cases) and `1/(1+·) ≤ 1` gives
the uniform constant. -/
theorem incident_symmDiff_corr_fin_div_c_le {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (u v : (↑((cubicExhaustion d).volume n) : Type _))
    (hadj : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v)
    (hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨x, hx⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
      ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨z, hz⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v))
    (hbind : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ)
        (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v})
      / correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ (1 + (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            * (latticeDistance d x z : ℝ)) ^ α)
          * Real.exp (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  classical
  set X : (↑((cubicExhaustion d).volume n) : Type _) := ⟨x, hx⟩ with hX
  set Z : (↑((cubicExhaustion d).volume n) : Type _) := ⟨z, hz⟩ with hZ
  set m : ℝ := globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact globalPseudoMassDist_nonneg hα _ _
  have hXZ : X ≠ Z := by rw [hX, hZ]; simpa [Subtype.ext_iff] using hxz
  have huv : u ≠ v := hadj.ne
  set c : ℝ := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; exact (correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x z hxz).1
  set Cinc : ℝ := (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m with hCinc
  -- The bridge `correlation_inducedGraph_cubic_le_correlationInfinite`, finite ≤ infinite.
  have bridge : ∀ a b : (↑((cubicExhaustion d).volume n) : Type _),
      correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {a, b}
        ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {a.val, b.val} := fun a b =>
    correlation_inducedGraph_cubic_le_correlationInfinite d (⟨J, 0, β⟩ : IsingParams ℝ) n a b
  -- "drop denominator" of the #4342 ratio bound: RHS ≤ Cinc.
  have drop : ∀ b : ℝ, 0 ≤ b → (1 + (m * (latticeDistance d x z : ℝ)) ^ α)
        * (1 / (1 + (m * b) ^ α)) * Real.exp m ≤ Cinc := by
    intro b hb
    rw [hCinc]
    have hden : (0 : ℝ) < 1 + (m * b) ^ α := by positivity
    have hle1 : 1 / (1 + (m * b) ^ α) ≤ 1 := by
      rw [div_le_one hden]; exact le_add_of_nonneg_right (pow_nonneg (mul_nonneg hm_nn hb) α)
    calc (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        ≤ (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * 1 * Real.exp m := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg m)
          exact mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m := by ring
  have hnotboth : ¬ ((X = u ∨ X = v) ∧ (Z = u ∨ Z = v)) := by
    rintro ⟨hXin, hZin⟩
    apply hxz_nonadj
    rcases hXin with rfl | rfl <;> rcases hZin with hZin | hZin
    · exact absurd hZin.symm hXZ
    · subst hZin; exact hadj
    · subst hZin; exact hadj.symm
    · exact absurd hZin.symm hXZ
  -- per-incident-dart `g{z,w}/c ≤ Cinc` for `w ∼ x`.
  have helper_x : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (latticeGraph d).Adj x w.val → z ≠ w.val →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, w.val} / c ≤ Cinc := by
    intro w hadjxw hzw
    have hr := correlationInfinite_incident_ratio_le hα hJ_pos hβ hxz hzw hadjxw hbind
    rw [← hc_def, ← hm_def] at hr
    exact hr.trans (drop _ (by positivity))
  -- per-incident-dart `g{x,w}/c ≤ Cinc` for `w ∼ z` (binding symmetry).
  have helper_z : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (latticeGraph d).Adj z w.val → x ≠ w.val →
      correlationInfinite (latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, w.val} / c ≤ Cinc := by
    intro w hadjzw hxw
    have hbind' : pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) z x
      = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
      rw [pseudoMassFromParamsAtPairDist_comm hα (cubicExhaustion d) _ z x]; exact hbind
    have hr := correlationInfinite_incident_ratio_le hα hJ_pos hβ (Ne.symm hxz) hxw hadjzw hbind'
    rw [show ({z, x} : Finset (Fin d → ℤ)) = {x, z} from Finset.pair_comm z x,
      show (latticeDistance d z x : ℝ) = (latticeDistance d x z : ℝ) from by
        rw [IsingModel.latticeDistance_comm], ← hc_def, ← hm_def] at hr
    exact hr.trans (drop _ (by positivity))
  rcases hpred with (rfl | rfl) | (rfl | rfl)
  · -- X = u: symmDiff {X,Z}{X,v} = {v,Z}.
    have hZv : Z ≠ v := fun h => hnotboth ⟨Or.inl rfl, Or.inr h⟩
    have hXv : X ≠ v := fun h => huv h
    rw [symmDiff_pair_pair_of_ne hXZ hXv (Ne.symm hZv)]
    have hadjxv : (latticeGraph d).Adj x v.val := hadj
    have hzv' : z ≠ v.val := fun h => hZv (by rw [hZ]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_x v hadjxv hzv')
    rw [Finset.pair_comm v Z]; exact (bridge Z v).trans_eq (by rw [hZ])
  · -- X = v: symmDiff {X,Z}{u,X} = {u,Z}.
    have hZu : Z ≠ u := fun h => hnotboth ⟨Or.inr rfl, Or.inl h⟩
    have hXu : X ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm u X, symmDiff_pair_pair_of_ne hXZ hXu (Ne.symm hZu)]
    have hadjxu : (latticeGraph d).Adj x u.val := hadj.symm
    have hzu' : z ≠ u.val := fun h => hZu (by rw [hZ]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_x u hadjxu hzu')
    rw [Finset.pair_comm u Z]; exact (bridge Z u).trans_eq (by rw [hZ])
  · -- Z = u: symmDiff {X,Z}{Z,v} = {v,X}.
    have hXv : X ≠ v := fun h => hnotboth ⟨Or.inr h, Or.inl rfl⟩
    have hZv : Z ≠ v := fun h => huv h
    rw [Finset.pair_comm X Z, symmDiff_pair_pair_of_ne hXZ.symm hZv (Ne.symm hXv)]
    have hadjzv : (latticeGraph d).Adj z v.val := hadj
    have hxv' : x ≠ v.val := fun h => hXv (by rw [hX]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_z v hadjzv hxv')
    rw [Finset.pair_comm v X]; exact (bridge X v).trans_eq (by rw [hX])
  · -- Z = v: symmDiff {X,Z}{u,Z} = {u,X}.
    have hXu : X ≠ u := fun h => hnotboth ⟨Or.inl h, Or.inr rfl⟩
    have hZu : Z ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm X Z, Finset.pair_comm u Z,
      symmDiff_pair_pair_of_ne hXZ.symm hZu (Ne.symm hXu)]
    have hadjzu : (latticeGraph d).Adj z u.val := hadj.symm
    have hxu' : x ≠ u.val := fun h => hXu (by rw [hX]; exact Subtype.ext h)
    refine le_trans (div_le_div_of_nonneg_right ?_ hc_pos.le) (helper_z u hadjzu hxu')
    rw [Finset.pair_comm u X]; exact (bridge X u).trans_eq (by rw [hX])

end Ambient
end IsingModel
