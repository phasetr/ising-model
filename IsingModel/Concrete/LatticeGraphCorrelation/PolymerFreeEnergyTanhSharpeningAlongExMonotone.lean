import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening

/-!
# Concrete along-ex polymer free-energy tanh-sharpening monotone wrappers

Narrow child module for 4 ℤ^d along-exhaustion polymer free-energy
tanh-sharpening monotone-in-(β,J) wrappers:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_beta_polymers_nonempty`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_J_polymers_nonempty`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_beta_polymers`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_J_polymers`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_tanh_*` lemma at
`G := IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real


/-- **ℤ^d along-ex: strict pFE(tanh) in β under polymers ≠ ∅**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_beta_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β₂ * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hβ₁ hJ hβ

/-- **ℤ^d along-ex: strict pFE(tanh) in J under polymers ≠ ∅**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_of_lt_in_J_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J₂)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hJ₁ hβ hJ

/-- **ℤ^d along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in
β**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_beta_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_beta_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hJ

/-- **ℤ^d along-ex: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in
J**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_strictMonoOn_J_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_strictMonoOn_J_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hβ

end Ambient
end IsingModel
