import IsingModel.ClusterExpansion.MayerCore.IndependentVanishing
import IsingModel.ClusterExpansion.MayerRootComponent

/-!
# Closed form of the Mayer term for non-interacting polymers (GJ §18.4–§18.5)

For a non-interacting polymer gas (distinct polymers pairwise compatible, i.e.
vertex-disjoint), the `n`-th Mayer term collapses to the diagonal
(`mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible`):
`mayerExpansionTerm G n t = ∑_P ϕ^T(P,…,P)·(t^|P|)^n`.  Each constant sequence
`(P,…,P)` is *fully* incompatible (a nonempty polymer is self-incompatible,
`PolymersIncompatible.self_of_isPolymer`), so its Ursell coefficient is the
classic single-cluster value `ϕ^T(P,…,P) = (-1)^(n-1)/n`
(`ursellCoefficient_complete_eq`).  Factoring this constant out yields the closed
form

`mayerExpansionTerm G n t = ((-1)^(n-1)/n) · ∑_P (t^|P|)^n`  (`n ≥ 1`).

Specialising to `n = 1, 2, 3` gives the first Mayer coefficients
`∑_P t^|P|`, `-½ ∑_P (t^|P|)²`, `⅓ ∑_P (t^|P|)³`; the `n = 3` value is the
non-interacting counterpart of the `n = 3` Ursell classification
(`ursellCoefficient_fin_three_*`, triangle value `1/3`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Ursell coefficient of a constant polymer sequence**: for `n ≥ 1` and a
nonempty polymer `P` of `G`, the constant sequence `(P,…,P)` is fully
incompatible (`P` is self-incompatible), so `ϕ^T(P,…,P) = (-1)^(n-1)/n`. -/
theorem ursellCoefficient_const_eq_of_isPolymer
    {G : SimpleGraph ι} [Fintype G.edgeSet]
    {P : Finset (Sym2 ι)} (hP : IsPolymer G P) {n : ℕ} (hn : 1 ≤ n) :
    ursellCoefficient (fun _ : Fin n => P) = (-1 : ℝ) ^ (n - 1) / (n : ℝ) := by
  refine ursellCoefficient_complete_eq hn (fun i j _ => ?_)
  exact PolymersIncompatible.self_of_isPolymer hP

/-- **Closed form of the Mayer term for a non-interacting polymer gas** (GJ
§18.4–§18.5): if distinct polymers of `G` are pairwise compatible
(vertex-disjoint), then for `n ≥ 1`

`mayerExpansionTerm G n t = ((-1)^(n-1)/n) · ∑_{P} (t^|P|)^n`.

The diagonal collapse (`mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible`)
reduces the term to `∑_P ϕ^T(P,…,P)·(t^|P|)^n`; every constant sequence is fully
incompatible, so `ϕ^T(P,…,P) = (-1)^(n-1)/n`
(`ursellCoefficient_const_eq_of_isPolymer`), a constant pulled out of the sum. -/
theorem mayerExpansionTerm_eq_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G,
      P ≠ Q → ¬ PolymersIncompatible P Q)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    mayerExpansionTerm G n t
      = (-1 : ℝ) ^ (n - 1) / (n : ℝ) * ∑ P ∈ allPolymers G, (t ^ P.card) ^ n := by
  rw [mayerExpansionTerm_eq_sum_diagonal_of_pairwise_compatible G hcompat hn t,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  rw [ursellCoefficient_const_eq_of_isPolymer (mem_allPolymers.mp hP) hn]

/-- **First Mayer coefficient (independent gas)**: `n = 1` case,
`mayerExpansionTerm G 1 t = ∑_{P} t^|P|`. -/
theorem mayerExpansionTerm_one_eq_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G,
      P ≠ Q → ¬ PolymersIncompatible P Q) (t : ℝ) :
    mayerExpansionTerm G 1 t = ∑ P ∈ allPolymers G, t ^ P.card := by
  rw [mayerExpansionTerm_eq_of_pairwise_disjoint G hcompat (le_refl 1) t]
  simp

/-- **Second Mayer coefficient (independent gas)**: `n = 2` case,
`mayerExpansionTerm G 2 t = -½ ∑_{P} (t^|P|)²`. -/
theorem mayerExpansionTerm_two_eq_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G,
      P ≠ Q → ¬ PolymersIncompatible P Q) (t : ℝ) :
    mayerExpansionTerm G 2 t = -(1 / 2) * ∑ P ∈ allPolymers G, (t ^ P.card) ^ 2 := by
  rw [mayerExpansionTerm_eq_of_pairwise_disjoint G hcompat (by norm_num) t]
  norm_num

/-- **Third Mayer coefficient (independent gas)**: `n = 3` case,
`mayerExpansionTerm G 3 t = ⅓ ∑_{P} (t^|P|)³`.  This is the non-interacting
analogue of the `n = 3` Ursell triangle value `1/3`
(`ursellCoefficient_complete_eq`); every constant triple `(P,P,P)` is a fully
incompatible triangle. -/
theorem mayerExpansionTerm_three_eq_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hcompat : ∀ P ∈ allPolymers G, ∀ Q ∈ allPolymers G,
      P ≠ Q → ¬ PolymersIncompatible P Q) (t : ℝ) :
    mayerExpansionTerm G 3 t = (1 / 3) * ∑ P ∈ allPolymers G, (t ^ P.card) ^ 3 := by
  rw [mayerExpansionTerm_eq_of_pairwise_disjoint G hcompat (by norm_num) t]
  norm_num

end IsingModel
