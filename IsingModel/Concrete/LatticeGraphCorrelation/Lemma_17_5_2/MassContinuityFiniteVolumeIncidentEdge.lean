import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeIncidentRatio
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentDivCTight
import IsingModel.Inequalities.SimonLieb

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3f: the finite-volume per-edge incident `/c` bound (p.312)

The finite-volume analogue of `incident_symmDiff_corr_fin_div_c_le_tight` (#4354): for a
non-adjacent in-box binding pair `x ≠ z` and an incident edge `{u,v}`, the c-cancelling reduced
correlation divided by `c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by the **constant** `(1+2^α)·e^{m⁻_FV}` — GJ
p.312's bounded `2A` (independent of the edge and of `d(x,z)`).  Non-adjacency gives
`r = d(x,z) ≥ 2`; the reduced pair (e.g. `{z,v}`, `v ∼ x`) has `d(z,v) ≥ r−1`, so the per-dart
ratio (PR-FV3e) has its denominator ratio bounded by `1+2^α` (`pseudoMass_denom_ratio_le`, #4353).

Unlike the infinite-volume route, the numerator is the *same* finite-volume correlation as the
denominator (no infinite-volume bridge): `⟨φ_a φ_b⟩` of the box subtype equals
`correlationAlongExhaustion {a.val, b.val} n`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **`pseudoMassFromParamsAtPairFV` is symmetric in the pair** (needed for the binding symmetry of
the `z`-incident edges): the finite-volume two-point function and the lattice distance are both
pair-symmetric. -/
theorem pseudoMassFromParamsAtPairFV_comm {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) (n : ℕ) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPairFV hα p n x z = pseudoMassFromParamsAtPairFV hα p n z x := by
  by_cases h : x = z
  · subst h; rfl
  · have hpos_xz : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun hh => h ((IsingModel.latticeDistance_eq_zero_iff d x z).mp hh))
    have hpos_zx : (0 : ℝ) < (IsingModel.latticeDistance d z x : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun hh => (Ne.symm h) ((IsingModel.latticeDistance_eq_zero_iff d z x).mp hh))
    rw [pseudoMassFromParamsAtPairFV_of_ne hα p n h hpos_xz,
      pseudoMassFromParamsAtPairFV_of_ne hα p n (Ne.symm h) hpos_zx,
      show ({z, x} : Finset (Fin d → ℤ)) = {x, z} from Finset.pair_comm z x]
    exact pseudoMassExt_congr_r hα
      (by rw [IsingModel.latticeDistance_comm d x z]) hpos_xz hpos_zx _

/-- **Finite-volume per-edge incident `/c` bound** (GJ p.312 `2A`): for a non-adjacent in-box
binding pair `x ≠ z` and an incident edge `{u,v}` of the induced cubic graph,
`corr_fin({⟨x⟩,⟨z⟩}△{u,v}) / ⟨φ_x φ_z⟩_{σ,A} ≤ (1+2^α)·e^{m⁻_FV}` — a **constant** (independent of
the edge and of `d(x,z)`).  Finite-volume mirror of #4354: the reduced pair's correlation is bounded
by the FV per-incident-dart ratio (PR-FV3e), then the denominator ratio by `1+2^α` (#4353) using
`d(reduced) ≥ r−1`. -/
theorem incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (IsingModel.latticeGraph d).Adj x z)
    (u v : (↑((cubicExhaustion d).volume n) : Type _))
    (hadj : (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v)
    (hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨x, hx⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
      ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨z, hz⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v))
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ)
        (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v})
      / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ (1 + (2 : ℝ) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) := by
  classical
  set X : (↑((cubicExhaustion d).volume n) : Type _) := ⟨x, hx⟩ with hX
  set Z : (↑((cubicExhaustion d).volume n) : Type _) := ⟨z, hz⟩ with hZ
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_nn : 0 ≤ m := by rw [hm_def]; exact (finiteRegionPseudoMassDistFV_pos hα hJ hβ hA).le
  have hXZ : X ≠ Z := by rw [hX, hZ]; simpa [Subtype.ext_iff] using hxz
  have huv : u ≠ v := hadj.ne
  set c : ℝ := Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n with hc_def
  have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hz
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub).1
  set Cinc : ℝ := (1 + (2 : ℝ) ^ α) * Real.exp m with hCinc
  -- `r = d(x,z) ≥ 2` from non-adjacency.
  have hr2 : (2 : ℝ) ≤ (latticeDistance d x z : ℝ) := by
    have h1 : 1 ≤ latticeDistance d x z :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hxz ((latticeDistance_eq_zero_iff d x z).mp h))
    have hne1 : latticeDistance d x z ≠ 1 :=
      fun h => hxz_nonadj ((latticeGraph_adj_iff_latticeDistance_eq_one d x z).mpr h)
    have : 2 ≤ latticeDistance d x z := by omega
    exact_mod_cast this
  -- numerator = denominator's correlation family (both finite-volume).
  have bridge : ∀ a b : (↑((cubicExhaustion d).volume n) : Type _),
      correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {a, b}
        = Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {a.val, b.val} n := by
    intro a b
    have hsub : ({a.val, b.val} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
      intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact a.property
      · exact b.property
    rw [correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hsub, correlationΛ_apply, liftFinset_pair hsub a.property
      b.property]
  -- "keep denominator": the FV ratio RHS at distance `b ≥ r−1` is bounded by `Cinc`.
  have drop_tight : ∀ b : ℝ, (latticeDistance d x z : ℝ) - 1 ≤ b →
      (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        ≤ Cinc := by
    intro b hb
    rw [hCinc]
    have hratio := pseudoMass_denom_ratio_le (α := α) (m := m)
      (r := (latticeDistance d x z : ℝ)) (s := b) hm_nn hr2 hb
    calc (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        = ((1 + (m * (latticeDistance d x z : ℝ)) ^ α) / (1 + (m * b) ^ α)) * Real.exp m := by
          rw [mul_one_div]
      _ ≤ (1 + (2 : ℝ) ^ α) * Real.exp m := mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg m)
  -- per-incident-dart `g{z,w}/c ≤ Cinc` for `w ∼ x`.
  have helper_x : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (IsingModel.latticeGraph d).Adj x w.val → z ≠ w.val →
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {z, w.val} n / c ≤ Cinc := by
    intro w hadjxw hzw
    have hr := correlationAlongExhaustion_incident_ratio_le_finiteRegionFV hα hJ hβ hA hxz hzw
      hadjxw hx hz w.property hbind
    rw [← hc_def, ← hm_def] at hr
    have htri : (latticeDistance d x z : ℝ) - 1 ≤ (latticeDistance d z w.val : ℝ) := by
      have hxw1 : latticeDistance d x w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d x w.val).mp hadjxw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ 1 + latticeDistance d z w.val := by
        rw [hxw1, hcomm] at htri_nat; omega
      have : (latticeDistance d x z : ℝ) ≤ 1 + (latticeDistance d z w.val : ℝ) := by
        exact_mod_cast hle
      linarith
    exact hr.trans (drop_tight _ htri)
  -- per-incident-dart `g{x,w}/c ≤ Cinc` for `w ∼ z` (binding symmetry).
  have helper_z : ∀ w : (↑((cubicExhaustion d).volume n) : Type _),
      (IsingModel.latticeGraph d).Adj z w.val → x ≠ w.val →
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, w.val} n / c ≤ Cinc := by
    intro w hadjzw hxw
    have hbind' : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n z x
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA := by
      rw [pseudoMassFromParamsAtPairFV_comm hα (⟨J, 0, β⟩ : IsingParams ℝ) n z x]; exact hbind
    have hr := correlationAlongExhaustion_incident_ratio_le_finiteRegionFV hα hJ hβ hA
      (Ne.symm hxz) hxw hadjzw hz hx w.property hbind'
    rw [show ({z, x} : Finset (Fin d → ℤ)) = {x, z} from Finset.pair_comm z x,
      show (latticeDistance d z x : ℝ) = (latticeDistance d x z : ℝ) from by
        rw [IsingModel.latticeDistance_comm], ← hc_def, ← hm_def] at hr
    have htri : (latticeDistance d x z : ℝ) - 1 ≤ (latticeDistance d x w.val : ℝ) := by
      have hzw1 : latticeDistance d z w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d z w.val).mp hadjzw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ latticeDistance d x w.val + 1 := by
        rw [hcomm, hzw1] at htri_nat; omega
      have : (latticeDistance d x z : ℝ) ≤ (latticeDistance d x w.val : ℝ) + 1 := by
        exact_mod_cast hle
      linarith
    exact hr.trans (drop_tight _ htri)
  have hnotboth : ¬ ((X = u ∨ X = v) ∧ (Z = u ∨ Z = v)) := by
    rintro ⟨hXin, hZin⟩
    apply hxz_nonadj
    rcases hXin with rfl | rfl <;> rcases hZin with hZin | hZin
    · exact absurd hZin.symm hXZ
    · subst hZin; exact hadj
    · subst hZin; exact hadj.symm
    · exact absurd hZin.symm hXZ
  rcases hpred with (rfl | rfl) | (rfl | rfl)
  · have hZv : Z ≠ v := fun h => hnotboth ⟨Or.inl rfl, Or.inr h⟩
    have hXv : X ≠ v := fun h => huv h
    rw [symmDiff_pair_pair_of_ne hXZ hXv (Ne.symm hZv)]
    have hadjxv : (IsingModel.latticeGraph d).Adj x v.val := hadj
    have hzv' : z ≠ v.val := fun h => hZv (by rw [hZ]; exact Subtype.ext h)
    rw [Finset.pair_comm v Z, bridge Z v, hZ]
    exact helper_x v hadjxv hzv'
  · have hZu : Z ≠ u := fun h => hnotboth ⟨Or.inr rfl, Or.inl h⟩
    have hXu : X ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm u X, symmDiff_pair_pair_of_ne hXZ hXu (Ne.symm hZu)]
    have hadjxu : (IsingModel.latticeGraph d).Adj x u.val := hadj.symm
    have hzu' : z ≠ u.val := fun h => hZu (by rw [hZ]; exact Subtype.ext h)
    rw [Finset.pair_comm u Z, bridge Z u, hZ]
    exact helper_x u hadjxu hzu'
  · have hXv : X ≠ v := fun h => hnotboth ⟨Or.inr h, Or.inl rfl⟩
    have hZv : Z ≠ v := fun h => huv h
    rw [Finset.pair_comm X Z, symmDiff_pair_pair_of_ne hXZ.symm hZv (Ne.symm hXv)]
    have hadjzv : (IsingModel.latticeGraph d).Adj z v.val := hadj
    have hxv' : x ≠ v.val := fun h => hXv (by rw [hX]; exact Subtype.ext h)
    rw [Finset.pair_comm v X, bridge X v, hX]
    exact helper_z v hadjzv hxv'
  · have hXu : X ≠ u := fun h => hnotboth ⟨Or.inl h, Or.inr rfl⟩
    have hZu : Z ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm X Z, Finset.pair_comm u Z,
      symmDiff_pair_pair_of_ne hXZ.symm hZu (Ne.symm hXu)]
    have hadjzu : (IsingModel.latticeGraph d).Adj z u.val := hadj.symm
    have hxu' : x ≠ u.val := fun h => hXu (by rw [hX]; exact Subtype.ext h)
    rw [Finset.pair_comm u X, bridge X u, hX]
    exact helper_z u hadjzu hxu'

end Ambient
end IsingModel
