import IsingModel.ClusterExpansion.MayerCore.IndependentCapstone

/-!
# Ising free energy as a Mayer expansion (non-interacting case, GJ §18.5)

For a non-interacting polymer gas (distinct polymers pairwise vertex-disjoint),
combining the polymer decomposition of the Ising free energy with the
non-interacting Mayer capstone gives the Ising free energy directly as a convergent
Mayer (cluster) expansion:
`freeEnergy G ⟨J,0,β⟩ = log 2 + (|E|/|ι|)·log cosh(βJ)
  + (∑'_n mayerExpansionTerm G n (tanh(βJ)))/|ι|`
(`freeEnergy_eq_tsum_mayer_of_pairwise_disjoint`).

The convergence condition `tanh(βJ)^|P| < 1` is automatic: polymers are non-empty
(`|P| ≥ 1`) and `tanh(βJ) < 1`.  This is the physical payoff of the cluster
expansion in the exactly-solvable regime — the free energy expressed through the
sum of its cluster terms.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The Mayer convergence condition is automatic for non-interacting polymers and
`0 ≤ β·J`: every polymer is non-empty and `tanh(βJ) < 1`, so `tanh(βJ)^|P| < 1`. -/
theorem tanh_pow_lt_one_of_mem_allPolymers
    (G : SimpleGraph ι) [Fintype G.edgeSet] {J β : ℝ} (hβJ : 0 ≤ β * J)
    {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    Real.tanh (β * J) ^ P.card < 1 := by
  have hPne : P.Nonempty := (mem_allPolymers.mp hP).nonempty
  exact pow_lt_one₀ (real_tanh_nonneg hβJ) (Real.tanh_lt_one _)
    (Finset.card_ne_zero.mpr hPne)

/-- **Ising free energy as a Mayer expansion (non-interacting case)** (GJ §18.5):
for pairwise vertex-disjoint polymers, `0 ≤ β·J` and `0 < |ι|`, the Ising free
energy equals its convergent Mayer (cluster) expansion,
`freeEnergy G ⟨J,0,β⟩ = log 2 + (|E|/|ι|)·log cosh(βJ)
  + (∑'_n mayerExpansionTerm G n (tanh(βJ)))/|ι|`.  Combines the polymer
decomposition `freeEnergy_eq_polymerFreeEnergy` with the non-interacting Mayer
capstone `polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_pairwise_disjoint`. -/
theorem freeEnergy_eq_tsum_mayer_of_pairwise_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι)
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne,
    polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_pairwise_disjoint G hpair
      (real_tanh_nonneg hβJ) (fun P hP => tanh_pow_lt_one_of_mem_allPolymers G hβJ hP)]

/-- **Ferromagnetic Ising free energy as a Mayer expansion (non-interacting case)**
(GJ §18.5): the Step-617 hypothesis form `0 ≤ J`, `0 < β`. -/
theorem freeEnergy_eq_tsum_mayer_of_pairwise_disjoint_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (hpair : (allPolymers G : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι :=
  freeEnergy_eq_tsum_mayer_of_pairwise_disjoint G J β (mul_nonneg hβ.le hJ) hne hpair

end IsingModel
