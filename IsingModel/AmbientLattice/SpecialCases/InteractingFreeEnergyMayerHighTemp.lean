import IsingModel.AmbientLattice.Exhaustion
import IsingModel.ClusterExpansion.MayerCore.InteractingFreeEnergyMayerHighTemp

/-!
# Λ-layer / along-exhaustion high-temperature Mayer expansion (GJ §18.5)

Λ-layer and along-exhaustion wrappers of the finite-graph high-temperature Mayer
expansion `freeEnergy_eq_tsum_mayer_of_high_temp`.  On a finite volume `Λ` (and at
each stage `n` of an exhaustion), under the explicit high-temperature conditions
on the induced graph, the per-site free energy equals its convergent cluster
expansion.

These are **per-volume** statements: the high-temperature conditions
`(1 + tanh βJ)^|E_Λ| < 2` and `e·|allPolymers (inducedGraph G Λ)|·tanh(βJ) < 1`
depend on the induced-graph edge count and polymer count, which grow with `|Λ|`,
so for fixed positive `tanh(βJ)` they fail at large volume.  A volume-uniform
Kotecky--Preiss / Dobrushin activity bound (not these per-volume conditions) is
what a genuine infinite-volume Mayer pressure identity requires; that is later
work.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386 (the
  cluster-expansion convergence mechanism for the pressure / free energy).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer high-temperature Mayer expansion** (GJ §18.5): on a nonempty finite
volume `Λ`, under the explicit high-temperature conditions on the induced graph,
the per-site free energy equals its convergent cluster expansion. -/
theorem freeEnergyΛ_eq_tsum_mayer_of_high_temp
    (G : SimpleGraph V) (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty)
    (hht : (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card < 2 ∧
      Real.exp 1 *
        ((IsingModel.allPolymers (inducedGraph G Λ)).card * Real.tanh (β * J)) < 1) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card (↑Λ : Type _) * Real.log (Real.cosh (β * J)) +
        (∑' n, IsingModel.mayerExpansionTerm (inducedGraph G Λ) n (Real.tanh (β * J))) /
            Fintype.card (↑Λ : Type _) :=
  IsingModel.freeEnergy_eq_tsum_mayer_of_high_temp (inducedGraph G Λ) J β hβJ
    (Finset.Nonempty.fintype_card_coe_pos hne) hht

/-- **Λ-layer ferromagnetic high-temperature Mayer expansion** (GJ §18.5):
hypotheses `0 ≤ J`, `0 < β`. -/
theorem freeEnergyΛ_eq_tsum_mayer_of_high_temp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty)
    (hht : (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card < 2 ∧
      Real.exp 1 *
        ((IsingModel.allPolymers (inducedGraph G Λ)).card * Real.tanh (β * J)) < 1) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card (↑Λ : Type _) * Real.log (Real.cosh (β * J)) +
        (∑' n, IsingModel.mayerExpansionTerm (inducedGraph G Λ) n (Real.tanh (β * J))) /
            Fintype.card (↑Λ : Type _) :=
  freeEnergyΛ_eq_tsum_mayer_of_high_temp G Λ J β (mul_nonneg hβ.le hJ) hne hht

/-- **Along-exhaustion high-temperature Mayer expansion** (GJ §18.5): at each
stage `n` of an exhaustion, on a nonempty volume `Λ.volume n` satisfying the
induced-graph high-temperature conditions, the per-site free energy equals its
convergent cluster expansion. -/
theorem freeEnergyAlongExhaustion_eq_tsum_mayer_of_high_temp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty)
    (hht : (1 + Real.tanh (β * J)) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card < 2 ∧
      Real.exp 1 * ((IsingModel.allPolymers (inducedGraph G (Λ.volume n))).card *
        Real.tanh (β * J)) < 1) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card (↑(Λ.volume n) : Type _) * Real.log (Real.cosh (β * J)) +
        (∑' k, IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J))) / Fintype.card (↑(Λ.volume n) : Type _) :=
  freeEnergyΛ_eq_tsum_mayer_of_high_temp G (Λ.volume n) J β hβJ hne hht

/-- **Along-exhaustion ferromagnetic high-temperature Mayer expansion** (GJ §18.5):
hypotheses `0 ≤ J`, `0 < β`. -/
theorem freeEnergyAlongExhaustion_eq_tsum_mayer_of_high_temp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : (Λ.volume n).Nonempty)
    (hht : (1 + Real.tanh (β * J)) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card < 2 ∧
      Real.exp 1 * ((IsingModel.allPolymers (inducedGraph G (Λ.volume n))).card *
        Real.tanh (β * J)) < 1) :
    freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n =
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            Fintype.card (↑(Λ.volume n) : Type _) * Real.log (Real.cosh (β * J)) +
        (∑' k, IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J))) / Fintype.card (↑(Λ.volume n) : Type _) :=
  freeEnergyAlongExhaustion_eq_tsum_mayer_of_high_temp G Λ J β (mul_nonneg hβ.le hJ) n hne hht

end Ambient

end IsingModel
