import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy

/-!
# Independent (non-interacting) polymer free energy (GJ §18.5)

When the polymers of `G` are pairwise vertex-disjoint (no two distinct polymers
share a vertex), the polymer gas is *non-interacting*: every subset of polymers
is a vertex-disjoint compatible family, so the polymer partition function
factorises and the polymer free energy is the sum of the single-polymer
contributions,
`∑_Γ ∏_{P ∈ Γ} t^|P| = ∏_{P} (1 + t^|P|)`,
`polymerFreeEnergy G t = ∑_{P} log(1 + t^|P|)`.
Substituting into the polymer decomposition of the Ising free energy gives the
closed form `f = log 2 + (|E|/|ι|)·log cosh(βJ) + (∑_P log(1+tanh(βJ)^|P|))/|ι|`.

This is the exactly-solvable independent-polymer case of the §18.4–§18.5 cluster
expansion (the general interacting case requires the Mayer–Montroll expansion).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Compatible families are all subsets, for pairwise-disjoint polymers**: if the
polymers of `G` are pairwise vertex-disjoint, then every subset of `allPolymers G`
is a vertex-disjoint compatible family, so `vdCompatiblePolymerFamilies G` is the
full powerset of `allPolymers G`. -/
theorem vdCompatiblePolymerFamilies_eq_powerset_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint) :
    vdCompatiblePolymerFamilies G = (allPolymers G).powerset := by
  ext Γ
  rw [mem_vdCompatiblePolymerFamilies, Finset.mem_powerset]
  refine ⟨fun h => h.1, fun hsub => ⟨hsub, ?_, ?_⟩⟩
  · intro P hP
    exact mem_allPolymers.mp (hsub hP)
  · exact hpair.mono (Finset.coe_subset.mpr hsub)

/-- **Independent-polymer partition factorisation** (GJ §18.5): for pairwise
vertex-disjoint polymers and any `t`, the polymer-family sum factorises,
`∑_Γ ∏_{P ∈ Γ} t^|P| = ∏_{P ∈ allPolymers G} (1 + t^|P|)`. -/
theorem vdPolymerFamilies_sum_eq_prod_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    (t : ℝ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      = ∏ P ∈ allPolymers G, (1 + t ^ P.card) := by
  rw [vdCompatiblePolymerFamilies_eq_powerset_of_pairwise_disjoint G hpair,
    Finset.prod_one_add]

/-- **Independent-polymer free energy** (GJ §18.5): for pairwise vertex-disjoint
polymers and `0 ≤ t`, the polymer free energy is the sum of the single-polymer
log contributions, `polymerFreeEnergy G t = ∑_{P} log(1 + t^|P|)`. -/
theorem polymerFreeEnergy_eq_sum_log_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    {t : ℝ} (ht0 : 0 ≤ t) :
    polymerFreeEnergy G t = ∑ P ∈ allPolymers G, Real.log (1 + t ^ P.card) := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_eq_prod_of_pairwise_disjoint G hpair, Real.log_prod]
  intro P _
  have hpow : (0 : ℝ) ≤ t ^ P.card := pow_nonneg ht0 _
  exact ne_of_gt (by linarith)

/-- **Independent-polymer Ising free energy** (GJ §18.5): for pairwise
vertex-disjoint polymers, `0 ≤ β·J` and `0 < |ι|`, the Ising free energy has the
closed form `f = log 2 + (|E|/|ι|)·log cosh(βJ) + (∑_P log(1+tanh(βJ)^|P|))/|ι|`.
Substitutes the independent-polymer free energy into the polymer decomposition
`freeEnergy_eq_polymerFreeEnergy`. -/
theorem freeEnergy_eq_sum_log_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι)
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑ P ∈ allPolymers G, Real.log (1 + Real.tanh (β * J) ^ P.card)) / Fintype.card ι := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne,
    polymerFreeEnergy_eq_sum_log_of_pairwise_disjoint G hpair (real_tanh_nonneg hβJ)]

end IsingModel
