import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanh

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy tanh-form high-temperature ceilings (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d`, under `0 ≤ β * J`, the
ceilings on the polymer free energy at activity `tanh (β * J)`: by the cluster-expansion
remainder `ε`, by `(1 + tanh (β * J)) ^ |E| − 1`, and — when that power is in addition below
`2` — strictly by `log 2`. These are the ℤ^d high-temperature convergence estimates of the
GJ §18.5 cluster expansion.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_eps_of_betaJ_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_eps_of_betaJ_nonneg
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_pow_sub_one_betaJ
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_pow_sub_one_of_betaJ_nonneg
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2`. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_log_two_of_pow_lt_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_log_two_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ hβJ n h_pow

end Ambient
end IsingModel
