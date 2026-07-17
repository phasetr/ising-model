import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBoundsTanh

/-!
# Concrete along-ex polymerFreeEnergyAlongExhaustion tanh HT bound wrappers

Narrow child module for 3 ℤ^d along-exhaustion
`polymerFreeEnergyAlongExhaustion_*_tanh_*` bound wrappers extracted
from `PolymerFreeEnergyHighTemperatureBoundsAlongEx.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_eps_of_betaJ_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_pow_sub_one_betaJ`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_log_two_of_pow_lt_two`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_tanh_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyHighTemperatureBoundsAlongEx`
declarations.
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
