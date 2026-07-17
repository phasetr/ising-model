import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Concrete polymerFreeEnergy_Λ tanh HT bound wrappers

Narrow child module for 3 ℤ^d Λ-direct `polymerFreeEnergy_Λ_*_tanh_*`
bound wrappers extracted from `PolymerFreeEnergyHighTemperatureBounds.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_tanh_le_eps_of_betaJ_nonneg`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_le_pow_sub_one_of_betaJ_nonneg`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_lt_log_two_of_pow_lt_two`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergy_Λ_tanh_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyHighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_eps_of_betaJ_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_le_pow_sub_one_of_betaJ_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_lt_log_two_of_pow_lt_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        < 2) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ hβJ h_pow

end Ambient
end IsingModel
