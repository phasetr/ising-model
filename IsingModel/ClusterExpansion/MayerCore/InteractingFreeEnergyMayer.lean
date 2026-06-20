import IsingModel.ClusterExpansion.MayerCore.IndependentFreeEnergyMayer
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll

/-!
# Ising free energy as a Mayer expansion (interacting case, GJ §18.5)

For a general (interacting) polymer gas — without the pairwise-vertex-disjoint
restriction of the non-interacting case — the convergent Mayer--Montroll identity
`mayer_identity_general_t` expresses the polymer free energy as its cluster
expansion under the Ko--Penrose-type convergence conditions.  Combining it with the
polymer decomposition `freeEnergy_eq_polymerFreeEnergy` gives the Ising free energy
directly as a convergent Mayer (cluster) expansion in the interacting regime:
`freeEnergy G ⟨J,0,β⟩ = log 2 + (|E|/|ι|)·log cosh(βJ)
  + (∑'_n mayerExpansionTerm G n (tanh(βJ)))/|ι|`
(`freeEnergy_eq_tsum_mayer_of_activity`), under the convergence hypotheses
`|ε(tanh βJ)| < 1` and `e·∑_P |tanh βJ|^|P| < 1`.

This is the interacting analogue of `IndependentFreeEnergyMayer`'s
`freeEnergy_eq_tsum_mayer_of_pairwise_disjoint`, and the finite-volume step toward
the §18.5 infinite-volume analyticity of the pressure.  The convergence
hypotheses are kept explicit; their high-temperature discharge and the
volume-uniform / infinite-volume limit are later work.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386 (the
  cluster-expansion convergence mechanism for the pressure / free energy).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Interacting Ising free energy as a Mayer expansion** (GJ §18.5).  Under the
Mayer--Montroll convergence conditions on the activity `t = tanh(βJ)`, the Ising
free energy at zero field equals its convergent cluster expansion.  Combines the
polymer decomposition `freeEnergy_eq_polymerFreeEnergy` with the general
Mayer--Montroll identity `mayer_identity_general_t`. -/
theorem freeEnergy_eq_tsum_mayer_of_activity
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι)
    (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card| < 1)
    (hact : Real.exp 1 *
        (∑ P ∈ allPolymers G, |Real.tanh (β * J)| ^ P.card) < 1) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne, mayer_identity_general_t G h_abs hact]

/-- **Ferromagnetic interacting Ising free energy as a Mayer expansion** (GJ §18.5):
the hypothesis form `0 ≤ J`, `0 < β`. -/
theorem freeEnergy_eq_tsum_mayer_of_activity_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card| < 1)
    (hact : Real.exp 1 *
        (∑ P ∈ allPolymers G, |Real.tanh (β * J)| ^ P.card) < 1) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι :=
  freeEnergy_eq_tsum_mayer_of_activity G J β (mul_nonneg hβ.le hJ) hne h_abs hact

end IsingModel
