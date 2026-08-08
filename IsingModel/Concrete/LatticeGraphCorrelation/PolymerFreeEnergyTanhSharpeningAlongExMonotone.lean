import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy strict growth in β and in J (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the strict growth of the
polymer free energy at activity `tanh (β * J)` in each of `β` and `J`, on a stage whose
induced graph carries at least one polymer and with the other parameter strictly positive:
as a two-point strict inequality from a nonnegative lower argument, and as
`StrictMonoOn (Set.Ici 0)`. This is the ℤ^d strict monotonicity of the GJ §18.5 cluster
expansion in the physical parameters.
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
