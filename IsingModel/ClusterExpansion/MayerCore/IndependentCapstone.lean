import IsingModel.ClusterExpansion.MayerCore.IndependentPolymer
import IsingModel.ClusterExpansion.MayerCore.IndependentVanishing
import IsingModel.ClusterExpansion.MayerCompleteContribution

/-!
# The Mayer expansion converges to the free energy (non-interacting case, GJ §18.5)

For a non-interacting polymer gas (distinct polymers pairwise vertex-disjoint) with
`0 ≤ t` and `t^|P| < 1` for every polymer `P`, the Mayer expansion converges to the
polymer free energy:
`HasSum (fun n => mayerExpansionTerm G n t) (polymerFreeEnergy G t)`
(`hasSum_mayerExpansionTerm_of_pairwise_disjoint`), and hence
`polymerFreeEnergy G t = ∑'_n mayerExpansionTerm G n t`
(`polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_pairwise_disjoint`).

This is the cluster-expansion *capstone* (`log Ξ = ∑_n` cluster terms) for the
exactly-solvable case: combining the diagonal collapse of the Mayer terms
(`mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible`, #3946), the
single-polymer multiplicity series
(`hasSum_singlePolymer_ursell_eq_log`, `∑_m ϕ^T(P,…,P)·(t^|P|)^m = log(1+t^|P|)`),
and the independent free energy `polymerFreeEnergy G t = ∑_P log(1+t^|P|)` (#3945).
The general interacting case requires the Kotecky–Preiss convergence estimate.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Mayer expansion converges to the polymer free energy (non-interacting
case)** (GJ §18.5): for pairwise vertex-disjoint polymers, `0 ≤ t`, and
`t^|P| < 1` for all `P`,
`HasSum (fun n => mayerExpansionTerm G n t) (polymerFreeEnergy G t)`. -/
theorem hasSum_mayerExpansionTerm_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    {t : ℝ} (ht0 : 0 ≤ t) (htconv : ∀ P ∈ allPolymers G, t ^ P.card < 1) :
    HasSum (fun n => mayerExpansionTerm G n t) (polymerFreeEnergy G t) := by
  classical
  rw [polymerFreeEnergy_eq_sum_log_of_pairwise_disjoint G hpair ht0]
  -- pairwise compatibility (for the diagonal collapse)
  have hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G, P ≠ Q →
      ¬ PolymersIncompatible P Q := by
    intro P hP Q hQ hPQ
    rw [PolymersIncompatible.iff_not_isPolymerVertexDisjoint, not_not]
    exact hpair hP hQ hPQ
  -- per-polymer diagonal contribution
  set gP : Finset (Sym2 ι) → ℕ → ℝ := fun P n =>
    ursellCoefficient (fun _ : Fin n => P) * (t ^ P.card) ^ n with hgP
  -- the n-th Mayer term is the sum of the diagonal contributions (all n)
  have hzero : ∀ P : Finset (Sym2 ι), gP P 0 = 0 := by
    intro P
    rw [hgP]
    refine mul_eq_zero.mpr (Or.inl ?_)
    exact ursellCoefficient_eq_zero_of_disconnected _ (fun h => h.nonempty.elim Fin.elim0)
  have hterm : ∀ n, mayerExpansionTerm G n t = ∑ P ∈ allPolymers G, gP P n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      rw [mayerExpansionTerm_zero]
      exact (Finset.sum_eq_zero (fun P _ => hzero P)).symm
    · exact mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible G hcompat hn1 t
  -- per-polymer HasSum to log(1 + t^|P|)
  have hP_sum : ∀ P ∈ allPolymers G,
      HasSum (gP P) (Real.log (1 + t ^ P.card)) := by
    intro P hP
    have habs : |t ^ P.card| < 1 := by
      rw [abs_of_nonneg (pow_nonneg ht0 _)]; exact htconv P hP
    have hsp := hasSum_singlePolymer_ursell_eq_log (mem_allPolymers.mp hP) habs
    have heq : (fun m : ℕ => ursellCoefficient (fun _ : Fin (m + 1) => P)
          * clusterSeqActivity t (fun _ : Fin (m + 1) => P))
        = fun m : ℕ => gP P (m + 1) := by
      funext m
      rw [hgP]
      congr 1
      rw [clusterSeqActivity]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [heq] at hsp
    have hshift := (hasSum_nat_add_iff (f := gP P) 1).mp hsp
    rw [Finset.sum_range_one, hzero P, add_zero] at hshift
    exact hshift
  -- combine over the finitely many polymers
  have hcomb := hasSum_sum hP_sum
  simp only [← hterm] at hcomb
  exact hcomb

/-- **Polymer free energy equals the Mayer `tsum` (non-interacting case)** (GJ
§18.5): the `tsum` form of `hasSum_mayerExpansionTerm_of_pairwise_disjoint`. -/
theorem polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    {t : ℝ} (ht0 : 0 ≤ t) (htconv : ∀ P ∈ allPolymers G, t ^ P.card < 1) :
    polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t :=
  (hasSum_mayerExpansionTerm_of_pairwise_disjoint G hpair ht0 htconv).tsum_eq.symm

end IsingModel
