import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# Concrete polymer free-energy tanh-sharpening β/J strict-mono wrappers

Narrow child module for 4 ℤ^d Λ-direct polymer free-energy
`tanh_*_of_polymers_nonempty` monotonicity-in-(β,J) wrappers extracted
from `PolymerFreeEnergyTanhSharpening.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_beta_of_polymers_nonempty`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_J_of_polymers_nonempty`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_beta_of_polymers_nonempty`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_J_of_polymers_nonempty`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergy_Λ_tanh_*_of_polymers_nonempty` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyTanhSharpening` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real


/-- **ℤ^d Λ: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β₂ * J)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hβ₁ hJ hβ

/-- **ℤ^d Λ: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J₂)) :=
  Ambient.polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hJ₁ hβ hJ

/-- **ℤ^d Λ: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_beta_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hJ

/-- **ℤ^d Λ: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**. -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_strictMonoOn_J_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hβ

end Ambient
end IsingModel
