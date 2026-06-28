import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeIncidentRatio
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityIncidentDivCTight
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDenomRatioGeneral
import IsingModel.Inequalities.SimonLieb

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3f: the finite-volume per-edge incident `/c` bound (p.312)

The finite-volume analogue of `incident_symmDiff_corr_fin_div_c_le_tight` (#4354): for an in-box
binding pair `x ≠ z` (**adjacent or not**) and an incident edge `{u,v}`, the c-cancelling reduced
correlation divided by `c = ⟨φ_x φ_z⟩_{σ,A}` is bounded by the **constant**
`(1+2^α)·e^{m⁻_FV} + (1+(m⁻_FV)^α)·e^{m⁻_FV}/2` — the first summand is GJ p.312's bounded `2A`
for the genuinely incident reduced pair; the second is the **self-edge** term that appears only when
`x ∼ z` (`{u,v}={x,z}`, so the symmetric difference is empty and the term is `1/c = (1+(m⁻_FV)^α)
e^{m⁻_FV}/2`, since `c = pseudoMassG α 1 m⁻_FV` at binding for an adjacent pair).

For the genuinely incident pair (e.g. `{z,v}`, `v ∼ x`) we have `d(z,v) ≥ 1` and
`d(x,z) ≤ 1 + d(z,v)`, so `d(x,z) ≤ 2·d(z,v)`; the per-dart ratio (PR-FV3e) then has its denominator
ratio bounded by `1+2^α` via the general `pseudoMass_denom_ratio_le_general` (which, unlike the
`2≤r` form, applies to the adjacent case `r = 1` too).

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

/-- **Finite-volume per-edge incident `/c` bound** (GJ p.312 `2A`): for an in-box binding pair
`x ≠ z` (adjacent or not) and an incident edge `{u,v}` of the induced cubic graph,
`corr_fin({⟨x⟩,⟨z⟩}△{u,v}) / ⟨φ_x φ_z⟩_{σ,A} ≤ (1+2^α)·e^{m⁻_FV} + (1+(m⁻_FV)^α)·e^{m⁻_FV}/2`.
The first summand is the bounded `2A` for a genuinely incident reduced pair (FV per-incident-dart
ratio PR-FV3e + `pseudoMass_denom_ratio_le_general`, valid for `r=1`); the second is the self-edge
contribution `1/c` arising only when `x ∼ z` and `{u,v}={x,z}` (empty symmetric difference, `c =
pseudoMassG α 1 m⁻_FV` at binding).  Adjacency-general mirror of #4354 / the non-adjacent FV
form. -/
theorem incident_symmDiff_corr_fin_div_c_le_tight_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z)
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
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
        + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
          * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) / 2 := by
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
  set Cself : ℝ := (1 + m ^ α) * Real.exp m / 2 with hCself
  have hCinc_nn : 0 ≤ Cinc := by
    rw [hCinc]; exact mul_nonneg (by positivity) (Real.exp_nonneg _)
  have hCself_nn : 0 ≤ Cself := by rw [hCself]; positivity
  have hr_nn : (0 : ℝ) ≤ (latticeDistance d x z : ℝ) := by positivity
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
  -- "keep denominator": the FV ratio RHS at distance `b` (`1 ≤ b`, `r ≤ 1+b`) is bounded by `Cinc`.
  have drop_tight : ∀ b : ℝ, 1 ≤ b → (latticeDistance d x z : ℝ) ≤ 1 + b →
      (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * (1 / (1 + (m * b) ^ α)) * Real.exp m
        ≤ Cinc := by
    intro b hb1 hb
    rw [hCinc]
    have hr2s : (latticeDistance d x z : ℝ) ≤ 2 * b := by linarith
    have hratio := pseudoMass_denom_ratio_le_general (α := α) (m := m)
      (r := (latticeDistance d x z : ℝ)) (s := b) hm_nn hr_nn (by linarith) hr2s
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
    have hs1 : (1 : ℝ) ≤ (latticeDistance d z w.val : ℝ) := by
      have h1 : 1 ≤ latticeDistance d z w.val :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hzw ((latticeDistance_eq_zero_iff d z w.val).mp h))
      exact_mod_cast h1
    have htri : (latticeDistance d x z : ℝ) ≤ 1 + (latticeDistance d z w.val : ℝ) := by
      have hxw1 : latticeDistance d x w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d x w.val).mp hadjxw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ 1 + latticeDistance d z w.val := by
        rw [hxw1, hcomm] at htri_nat; omega
      exact_mod_cast hle
    exact hr.trans (drop_tight _ hs1 htri)
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
    have hs1 : (1 : ℝ) ≤ (latticeDistance d x w.val : ℝ) := by
      have h1 : 1 ≤ latticeDistance d x w.val :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hxw ((latticeDistance_eq_zero_iff d x w.val).mp h))
      exact_mod_cast h1
    have htri : (latticeDistance d x z : ℝ) ≤ 1 + (latticeDistance d x w.val : ℝ) := by
      have hzw1 : latticeDistance d z w.val = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d z w.val).mp hadjzw
      have htri_nat : latticeDistance d x z
          ≤ latticeDistance d x w.val + latticeDistance d w.val z :=
        latticeDistance_triangle d x w.val z
      have hcomm : latticeDistance d w.val z = latticeDistance d z w.val :=
        latticeDistance_comm d w.val z
      have hle : latticeDistance d x z ≤ latticeDistance d x w.val + 1 := by
        rw [hcomm, hzw1] at htri_nat; omega
      have hcast : (latticeDistance d x z : ℝ) ≤ (latticeDistance d x w.val : ℝ) + 1 := by
        exact_mod_cast hle
      linarith
    exact hr.trans (drop_tight _ hs1 htri)
  by_cases hboth : (X = u ∨ X = v) ∧ (Z = u ∨ Z = v)
  · -- self edge `{u,v} = {X,Z}` (only possible when `x ∼ z`): `symmDiff = ∅`, term `1/c = Cself`.
    obtain ⟨hXin, hZin⟩ := hboth
    have hself : symmDiff ({X, Z} : Finset _) {u, v} = ∅
        ∧ (IsingModel.latticeGraph d).Adj x z := by
      rcases hXin with rfl | rfl
      · rcases hZin with hh | hh
        · exact absurd hh.symm hXZ
        · subst hh; exact ⟨by rw [symmDiff_self, Finset.bot_eq_empty], hadj⟩
      · rcases hZin with hh | hh
        · subst hh
          exact ⟨by rw [Finset.pair_comm Z X, symmDiff_self, Finset.bot_eq_empty], hadj.symm⟩
        · exact absurd hh.symm hXZ
    obtain ⟨hsymm0, hadjxz⟩ := hself
    rw [hsymm0, correlation_empty]
    have hr1 : (latticeDistance d x z : ℝ) = 1 := by
      have h1 : latticeDistance d x z = 1 :=
        (latticeGraph_adj_iff_latticeDistance_eq_one d x z).mp hadjxz
      exact_mod_cast h1
    have hc_eq : c = pseudoMassG α (latticeDistance d x z : ℝ) m := by
      rw [hc_def, correlationAlongExhaustion_eq_pseudoMassG_finiteVolume hα hJ hβ hxz hxzsub, hbind]
    have hkey : (1 : ℝ) / c = Cself := by
      rw [hc_eq, hr1, hCself, pseudoMassG, mul_one, one_div_div, Real.exp_neg]
      have hne : Real.exp m ≠ 0 := Real.exp_ne_zero m
      field_simp
    rw [hkey]
    exact le_add_of_nonneg_left hCinc_nn
  · -- genuinely incident edge `{u,v} ≠ {X,Z}`: existing 4-way argument, then `≤ Cinc ≤ Cinc+Cself`.
    have hnotboth := hboth
    rcases hpred with (rfl | rfl) | (rfl | rfl)
    · have hZv : Z ≠ v := fun h => hnotboth ⟨Or.inl rfl, Or.inr h⟩
      have hXv : X ≠ v := fun h => huv h
      rw [symmDiff_pair_pair_of_ne hXZ hXv (Ne.symm hZv)]
      have hadjxv : (IsingModel.latticeGraph d).Adj x v.val := hadj
      have hzv' : z ≠ v.val := fun h => hZv (by rw [hZ]; exact Subtype.ext h)
      rw [Finset.pair_comm v Z, bridge Z v, hZ]
      exact (helper_x v hadjxv hzv').trans (le_add_of_nonneg_right hCself_nn)
    · have hZu : Z ≠ u := fun h => hnotboth ⟨Or.inr rfl, Or.inl h⟩
      have hXu : X ≠ u := fun h => huv h.symm
      rw [Finset.pair_comm u X, symmDiff_pair_pair_of_ne hXZ hXu (Ne.symm hZu)]
      have hadjxu : (IsingModel.latticeGraph d).Adj x u.val := hadj.symm
      have hzu' : z ≠ u.val := fun h => hZu (by rw [hZ]; exact Subtype.ext h)
      rw [Finset.pair_comm u Z, bridge Z u, hZ]
      exact (helper_x u hadjxu hzu').trans (le_add_of_nonneg_right hCself_nn)
    · have hXv : X ≠ v := fun h => hnotboth ⟨Or.inr h, Or.inl rfl⟩
      have hZv : Z ≠ v := fun h => huv h
      rw [Finset.pair_comm X Z, symmDiff_pair_pair_of_ne hXZ.symm hZv (Ne.symm hXv)]
      have hadjzv : (IsingModel.latticeGraph d).Adj z v.val := hadj
      have hxv' : x ≠ v.val := fun h => hXv (by rw [hX]; exact Subtype.ext h)
      rw [Finset.pair_comm v X, bridge X v, hX]
      exact (helper_z v hadjzv hxv').trans (le_add_of_nonneg_right hCself_nn)
    · have hXu : X ≠ u := fun h => hnotboth ⟨Or.inl h, Or.inr rfl⟩
      have hZu : Z ≠ u := fun h => huv h.symm
      rw [Finset.pair_comm X Z, Finset.pair_comm u Z,
        symmDiff_pair_pair_of_ne hXZ.symm hZu (Ne.symm hXu)]
      have hadjzu : (IsingModel.latticeGraph d).Adj z u.val := hadj.symm
      have hxu' : x ≠ u.val := fun h => hXu (by rw [hX]; exact Subtype.ext h)
      rw [Finset.pair_comm u X, bridge X u, hX]
      exact (helper_z u hadjzu hxu').trans (le_add_of_nonneg_right hCself_nn)

end Ambient
end IsingModel
