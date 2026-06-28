import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.CubicDerivativeProfileCancelling
import IsingModel.Concrete.LatticeGraphCorrelation.CubicShellInfiniteVolumeBound
import IsingModel.Inequalities.SimonLieb

/-!
# Infinite-volume bridge for the c-cancelling incident term (GJ §17.5 Theorem 17.5.1, p.312)

For **non-adjacent** distinct sites `x, z` (GJ's regime: large separation, where `c = ⟨σ_x σ_z⟩` is
exponentially small), no induced-graph edge contains both `⟨x⟩` and `⟨z⟩`, so the c-cancelling
incident summand `corr_fin({⟨x⟩,⟨z⟩}△{u,v})`
(from `derivative_profile_cubic_le_lebowitz_cancelling`)
reduces — for an incident edge `{u,v}` — to a single finite-volume two-point function
`corr_fin{⟨z⟩,w}` or `corr_fin{⟨x⟩,w}` (`w` the non-incident endpoint), which is dominated by the
infinite-volume two-point function `corr∞{z,w}` / `corr∞{x,w}`
(`correlation_inducedGraph_cubic_le_correlationInfinite`).

This module supplies:

* `incident_symmDiff_corr_fin_le_infinite` — the per-edge reduction;
* `derivative_profile_cubic_le_infiniteVolume_lebowitz_cancelling` — c-cancelling counterpart of
  `derivative_profile_cubic_le_infiniteVolume_lebowitz`, with the `J·|incident|` count replaced
  by the infinite-volume reduced cross sum `J·∑_{e incident}(g{x,u}+g{x,v}+g{z,u}+g{z,v})`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Finset

/-- **Per-edge infinite-volume reduction of the c-cancelling incident summand** (GJ p.312, large
separation): for non-adjacent `x, z` and an incident edge `{u,v}` of the induced cubic graph
(`⟨x⟩ ∈ {u,v} ∨ ⟨z⟩ ∈ {u,v}`), the reduced correlation `corr_fin({⟨x⟩,⟨z⟩}△{u,v})` is bounded by the
infinite-volume cross sum `g{x,u}+g{x,v}+g{z,u}+g{z,v}` (where `g{a,b} = correlationInfinite …
{a,b}`).  Because `x, z` are non-adjacent, no edge contains both `⟨x⟩` and `⟨z⟩`, so exactly one of
`⟨x⟩,⟨z⟩` lies in `{u,v}`; the symmetric difference collapses to a single two-point set, dominated
by its infinite-volume value (`correlation_inducedGraph_cubic_le_correlationInfinite`); the other
three terms are non-negative (`correlationInfinite_nonneg`). -/
theorem incident_symmDiff_corr_fin_le_infinite (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hx : x ∈ (cubicExhaustion d).volume n)
    (hz : z ∈ (cubicExhaustion d).volume n)
    (hxz : x ≠ z) (hxz_nonadj : ¬ (latticeGraph d).Adj x z)
    (u v : (↑((cubicExhaustion d).volume n) : Type _))
    (hadj : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v)
    (hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨x, hx⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
      ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨ (⟨z, hz⟩ :
        (↑((cubicExhaustion d).volume n) : Type _)) = v)) :
    correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ)
        (symmDiff {(⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)), ⟨z, hz⟩} {u, v})
      ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} +
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} +
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} +
          correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} := by
  classical
  set X : (↑((cubicExhaustion d).volume n) : Type _) := ⟨x, hx⟩ with hX
  set Z : (↑((cubicExhaustion d).volume n) : Type _) := ⟨z, hz⟩ with hZ
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hXZ : X ≠ Z := by rw [hX, hZ]; simpa [Subtype.ext_iff] using hxz
  have huv : u ≠ v := hadj.ne
  -- abbreviations for the infinite-volume two-point functions.
  set gxu := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} with hgxu
  set gxv := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} with hgxv
  set gzu := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} with hgzu
  set gzv := correlationInfinite (latticeGraph d) (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} with hgzv
  have hgxu_nn : 0 ≤ gxu := correlationInfinite_nonneg _ _ _ hf _
  have hgxv_nn : 0 ≤ gxv := correlationInfinite_nonneg _ _ _ hf _
  have hgzu_nn : 0 ≤ gzu := correlationInfinite_nonneg _ _ _ hf _
  have hgzv_nn : 0 ≤ gzv := correlationInfinite_nonneg _ _ _ hf _
  -- no induced edge contains both ⟨x⟩ and ⟨z⟩ (non-adjacency).
  have hnotboth : ¬ ((X = u ∨ X = v) ∧ (Z = u ∨ Z = v)) := by
    rintro ⟨hXin, hZin⟩
    apply hxz_nonadj
    rcases hXin with rfl | rfl <;> rcases hZin with hZin | hZin
    · exact absurd hZin.symm hXZ
    · subst hZin; exact hadj
    · subst hZin; exact hadj.symm
    · exact absurd hZin.symm hXZ
  -- bridge: finite ≤ infinite for the lifted pair {a,b}.
  have bridge : ∀ a b : (↑((cubicExhaustion d).volume n) : Type _),
      correlation (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n))
          (⟨J, 0, β⟩ : IsingParams ℝ) {a, b}
        ≤ correlationInfinite (latticeGraph d) (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {a.val, b.val} := fun a b =>
    correlation_inducedGraph_cubic_le_correlationInfinite d (⟨J, 0, β⟩ : IsingParams ℝ) n a b
  rcases hpred with (rfl | rfl) | (rfl | rfl)
  · -- X = u, so Z ≠ u (=X), and Z ≠ v (else both); symmDiff {X,Z}{X,v} = {v,Z}.
    have hZv : Z ≠ v := fun h => hnotboth ⟨Or.inl rfl, Or.inr h⟩
    have hXv : X ≠ v := fun h => huv h
    rw [symmDiff_pair_pair_of_ne hXZ hXv (Ne.symm hZv)]
    refine le_trans (bridge v Z) ?_
    have : correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {v.val, Z.val} = gzv := by
      rw [hgzv, hZ, Finset.pair_comm]
    rw [this]; linarith
  · -- X = v, so Z ≠ v (=X), and Z ≠ u (else both); symmDiff {X,Z}{u,X} = {u,Z}.
    have hZu : Z ≠ u := fun h => hnotboth ⟨Or.inr rfl, Or.inl h⟩
    have hXu : X ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm u X, symmDiff_pair_pair_of_ne hXZ hXu (Ne.symm hZu)]
    refine le_trans (bridge u Z) ?_
    have : correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {u.val, Z.val} = gzu := by
      rw [hgzu, hZ, Finset.pair_comm]
    rw [this]; linarith
  · -- Z = u, so X ≠ u (=Z), and X ≠ v (else both); symmDiff {X,Z}{Z,v} = {v,X}.
    have hXv : X ≠ v := fun h => hnotboth ⟨Or.inr h, Or.inl rfl⟩
    have hZv : Z ≠ v := fun h => huv h
    rw [Finset.pair_comm X Z, symmDiff_pair_pair_of_ne hXZ.symm hZv (Ne.symm hXv)]
    refine le_trans (bridge v X) ?_
    have : correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {v.val, X.val} = gxv := by
      rw [hgxv, hX, Finset.pair_comm]
    rw [this]; linarith
  · -- Z = v, so X ≠ v (=Z), and X ≠ u (else both); symmDiff {X,Z}{u,Z} = {u,X}.
    have hXu : X ≠ u := fun h => hnotboth ⟨Or.inl h, Or.inr rfl⟩
    have hZu : Z ≠ u := fun h => huv h.symm
    rw [Finset.pair_comm X Z, Finset.pair_comm u Z,
      symmDiff_pair_pair_of_ne hXZ.symm hZu (Ne.symm hXu)]
    refine le_trans (bridge u X) ?_
    have : correlationInfinite (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {u.val, X.val} = gxu := by
      rw [hgxu, hX, Finset.pair_comm]
    rw [this]; linarith

/-- **c-cancelling infinite-volume Lebowitz bound for the cubic β-derivative profile** (GJ §17.5,
p.312, large separation): for `0 ≤ J`, `0 < β`, distinct **non-adjacent** sites `x, z` with
`{x,z} ⊆ volume n`, the β-derivative of the finite-volume profile is bounded by `J` times the
infinite-volume Lebowitz two-point cross sum over the stage-`n` edges, plus `J` times the
infinite-volume reduced incident cross sum:
`∂_β c_n ≤ J·∑_{⟨u,v⟩∈E}[g{x,u}g{z,v}+g{x,v}g{z,u}]`
`+ J·∑_{e incident}(g{x,u}+g{x,v}+g{z,u}+g{z,v})`,
where `g{a,b} = correlationInfinite (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {a,b}`.  Unlike
`derivative_profile_cubic_le_infiniteVolume_lebowitz` (whose incident term is the `O(1)` *count*
`J·|incident|`, which blows up after dividing by the exponentially small `c = ⟨σ_x σ_z⟩`), the
incident term here is a sum of infinite-volume two-point functions — GJ's bounded `2A` mechanism —
whose `/c` ratios stay bounded.  Composes `derivative_profile_cubic_le_lebowitz_cancelling` (#4340)
with the termwise finite ≤ infinite bridge `correlation_inducedGraph_cubic_le_correlationInfinite`
(Lebowitz part, products monotone since correlations are non-negative) and the per-edge incident
reduction `incident_symmDiff_corr_fin_le_infinite`. -/
theorem derivative_profile_cubic_le_infiniteVolume_lebowitz_cancelling (d : ℕ) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hxz_nonadj : ¬ (latticeGraph d).Adj x z) {n : ℕ}
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    deriv (fun β' => correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
      ≤ J * ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} *
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val} +
              correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} *
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val},
            fun u v => by ring⟩ e
        + J * ∑ e ∈ (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).edgeFinset.filter
            (fun e => (⟨x, hsub (Finset.mem_insert_self x {z})⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e ∨
              (⟨z, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))⟩ :
                (↑((cubicExhaustion d).volume n) : Type _)) ∈ e),
          Sym2.lift ⟨fun u v =>
              correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, u.val} +
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {x, v.val} +
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, u.val} +
                correlationInfinite (latticeGraph d) (cubicExhaustion d)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {z, v.val},
            fun u v => by ring⟩ e := by
  classical
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  refine (derivative_profile_cubic_le_lebowitz_cancelling d J β hJ hβ hxz hsub).trans ?_
  apply add_le_add
  · -- Lebowitz cross-sum part: identical to the tight infinite-volume bridge.
    apply mul_le_mul_of_nonneg_left _ hJ
    apply Finset.sum_le_sum
    intro e _he
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    have bxu := correlation_inducedGraph_cubic_le_correlationInfinite d
      (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ u
    have bzv := correlation_inducedGraph_cubic_le_correlationInfinite d
      (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ v
    have bxv := correlation_inducedGraph_cubic_le_correlationInfinite d
      (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨x, hx⟩ v
    have bzu := correlation_inducedGraph_cubic_le_correlationInfinite d
      (⟨J, 0, β⟩ : IsingParams ℝ) n ⟨z, hz⟩ u
    refine add_le_add
      (mul_le_mul bxu bzv (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
      (mul_le_mul bxv bzu (gks_first _ _ hf _) (correlationInfinite_nonneg _ _ _ hf _))
  · -- Incident part: per-edge infinite-volume reduction.
    apply mul_le_mul_of_nonneg_left _ hJ
    apply Finset.sum_le_sum
    intro e he_mem
    rw [Finset.mem_filter] at he_mem
    obtain ⟨heE, hpred_sym2⟩ := he_mem
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    simp only [Sym2.lift_mk]
    have hadj : (inducedGraph (latticeGraph d) ((cubicExhaustion d).volume n)).Adj u v :=
      SimpleGraph.mem_edgeFinset.mp heE
    have hpred : ((⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨
          (⟨x, hx⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = v) ∨
        ((⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = u ∨
          (⟨z, hz⟩ : (↑((cubicExhaustion d).volume n) : Type _)) = v) := by
      rcases hpred_sym2 with h | h
      · exact Or.inl (Sym2.mem_iff.mp h)
      · exact Or.inr (Sym2.mem_iff.mp h)
    exact incident_symmDiff_corr_fin_le_infinite d J β hJ hβ hx hz hxz hxz_nonadj u v hadj hpred

end Ambient
end IsingModel
