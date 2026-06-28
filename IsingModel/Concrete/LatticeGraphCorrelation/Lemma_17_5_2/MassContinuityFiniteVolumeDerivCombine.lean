import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeCrossSum
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityFiniteVolumeIncidentSum
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityScaledSummable
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicDerivativeProfileCancelling

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV3h: the combined finite-volume β-derivative `/c` bound (p.312)

The finite-volume analogue of `combined_derivative_div_c_bound_tight` (#4356) — but entirely at the
finite volume `A = volume n` (no infinite-volume bridge, no `n → ∞` limit).  From the finite
c-cancelling Lebowitz derivative (#4340), dividing by `c = ⟨φ_x φ_z⟩_{σ,A}`:

`∂_β c_A / c ≤ J·[2(1+(m⁻_FV·d(x,z))^α)e^{m⁻_FV}·C(1+d(x,z))^{−(2α−d)}] + J·[4d(1+2^α)e^{m⁻_FV}]`.

The cross part: bridge the subtype-correlation cross-sum (#4340 output) to the
`correlationAlongExhaustion` form, then the FV cross-sum `/c` bound (PR-FV3d) + the `m⁻_FV`-scaled
HLS convolution (#4350).  The incident part: the FV bounded incident-sum `/c` bound (PR-FV3g).
Both fit GJ's `m⁻^{2α}·dm⁻/dσ ≤ const`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Core combined finite-volume β-derivative `/c` bound** (GJ p.312): the body of
`combined_derivative_div_c_bound_tight_finiteRegionFV` with the cross-sum dart-profile convolution
constant `C` supplied as a **parameter** (via `hCconv`) rather than obtained internally.  This lets
both the per-scale version (`C` from `dart_profile_sum_le_convolution`) and the **mass-uniform**
version (`C` from `dart_profile_sum_le_convolution_mass_uniform`, the same `C` for all `m⁻_FV ≥
mmin`) share the body, the latter being what the uniform-in-`β` Lipschitz estimate needs. -/
theorem combined_derivative_div_c_bound_core_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
    (C : ℝ)
    (hCconv : ∀ x' z' : Fin d → ℤ,
      ∑ dt : (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).Dart,
          (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x' dt.fst.val : ℝ)) ^ α))
            * (1 / (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d z' dt.snd.val : ℝ)) ^ α))
        ≤ C * (1 + (latticeDistance d x' z' : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) :
      deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
        / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
          + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            / 2)) := by
  classical
  set m : ℝ := finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA with hm_def
  have hm_pos : 0 < m := by rw [hm_def]; exact finiteRegionPseudoMassDistFV_pos hα hJ hβ hA
  have hc_pos : 0 < Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n := by
    have hxzsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
      intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hx
      · exact hz
    exact (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hxzsub).1
  have hpow : (0 : ℝ) ≤ (m * (latticeDistance d x z : ℝ)) ^ α :=
    pow_nonneg (mul_nonneg hm_pos.le (by positivity)) α
  have hcoef_nn : (0 : ℝ) ≤ 2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_nonneg _)
  -- per-vertex bridge: subtype correlation = `correlationAlongExhaustion` of the `.val` pair.
  have vbridge : ∀ (a : Fin d → ℤ) (ha : a ∈ (cubicExhaustion d).volume n)
      (w : (↑((cubicExhaustion d).volume n) : Type _)),
      correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {(⟨a, ha⟩ : (↑((cubicExhaustion d).volume n) : Type _)), w}
        = Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {a, w.val} n := by
    intro a ha w
    have hsub : ({a, w.val} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
      intro y hy; rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact w.property
    rw [correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hsub, correlationΛ_apply, liftFinset_pair hsub ha w.property]
  -- bridge the cross-sum (subtype form, #4340) to the `correlationAlongExhaustion` form (PR-FV3d).
  have hcross_eq :
      (∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, u} *
              correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, v} +
            correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, v} *
              correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, u},
          fun u v => by ring⟩ e)
      = ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} n +
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} n *
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} n,
          fun u v => by ring⟩ e := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    rw [vbridge x hx u, vbridge z hz v, vbridge x hx v, vbridge z hz u]
  -- cross-sum `/c` ≤ profile-convolution bound.
  have hcross : (∑ e ∈ (inducedGraph (IsingModel.latticeGraph d)
          ((cubicExhaustion d).volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, u} *
              correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, v} +
            correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨x, hx⟩, v} *
              correlation (inducedGraph (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {⟨z, hz⟩, u},
          fun u v => by ring⟩ e)
        / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ 2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m
          * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))) := by
    rw [hcross_eq]
    exact (cross_sum_div_c_le_dart_profile_finiteRegionFV hα hJ hβ hA hxz hx hz hbind).trans
      (mul_le_mul_of_nonneg_left (hCconv x z) hcoef_nn)
  -- incident `/c` bound.
  have hinc := incident_sum_corr_fin_div_c_le_tight_finiteRegionFV hα hJ hβ hA hx hz hxz hbind
  rw [← hm_def] at hinc
  -- combine.
  rw [div_le_iff₀ hc_pos]
  refine (derivative_profile_cubic_le_lebowitz_cancelling d J β hJ.le hβ hxz
    (by intro w hw; rw [Finset.mem_insert, Finset.mem_singleton] at hw;
        rcases hw with rfl | rfl; exacts [hx, hz])).trans ?_
  have hSc := (div_le_iff₀ hc_pos).mp hcross
  have hSi := (div_le_iff₀ hc_pos).mp hinc
  calc J * _ + J * _
      ≤ J * ((2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ))))) *
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n)
        + J * (((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2)) *
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n) :=
        add_le_add (mul_le_mul_of_nonneg_left hSc hJ.le)
          (mul_le_mul_of_nonneg_left hSi hJ.le)
    _ = (J * (2 * (1 + (m * (latticeDistance d x z : ℝ)) ^ α) * Real.exp m
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
          + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α) * Real.exp m
              + (1 + m ^ α) * Real.exp m / 2)))
          * Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n := by ring

/-- **Combined finite-volume β-derivative `/c` bound** (GJ p.312): for `1≤α`, `1≤d`, `d<2α<2d`,
`0<J`, `0<β`, an in-box binding pair `x≠z` (adjacent or not),
`∃ C>0, ∂_β c_A / c ≤ J·[2(1+(m⁻_FV·r)^α)e^{m⁻_FV}·C(1+r)^{−(2α−d)}]
+ J·[4d((1+2^α)e^{m⁻_FV} + (1+(m⁻_FV)^α)e^{m⁻_FV}/2)]` (`r=d(x,z)`, `c=c_A=⟨φ_xφ_z⟩_{σ,A}`,
`m⁻_FV=finiteRegionPseudoMassDistFV`).  The per-scale form: obtains `C` from the `m⁻_FV`-scaled
convolution `dart_profile_sum_le_convolution` and applies the core. -/
theorem combined_derivative_div_c_bound_tight_finiteRegionFV {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (hαd : d < 2 * α) (hαd2 : α < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {n : ℕ}
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hx : x ∈ (cubicExhaustion d).volume n) (hz : z ∈ (cubicExhaustion d).volume n)
    (hbind : pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z
      = finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) :
    ∃ C : ℝ, 0 < C ∧
      deriv (fun β' => Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d)
          (cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
        / Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} n
      ≤ J * (2 * (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA
              * (latticeDistance d x z : ℝ)) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            * (C * (1 + (latticeDistance d x z : ℝ)) ^ (-(2 * (α : ℝ) - (d : ℝ)))))
        + J * ((4 * d : ℝ) * ((1 + (2 : ℝ) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
          + (1 + (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA) ^ α)
            * Real.exp (finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA)
            / 2)) := by
  have hm_pos : 0 < finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA :=
    finiteRegionPseudoMassDistFV_pos hα hJ hβ hA
  obtain ⟨C, hC, hCconv⟩ :=
    dart_profile_sum_le_convolution (d := d) hd hαd hαd2 hm_pos (n := n)
  exact ⟨C, hC, combined_derivative_div_c_bound_core_finiteRegionFV hα hJ hβ hA hxz hx hz hbind
    C hCconv⟩

end Ambient
end IsingModel
