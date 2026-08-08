import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds

/-!
# ℤ^d §18.5 AlongExhaustion polymerFreeEnergy tanh-bound / `hasDerivAt` wrappers

Instantiates the along-exhaustion polymer free-energy `tanh`-form upper bound, its closed
form `log (1 + ε)`, and its derivative at `IsingModel.latticeGraph d`,
the ℤ^d shape of the GJ §18.5 estimates.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy_tanh ≤ |E|·tanh** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_card_mul
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.tanh (β * J) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_le_card_mul
    (IsingModel.latticeGraph d) Λ hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy = log(1 + ε(t))**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_eq_log_one_add_eps
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_log_one_add_eps
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_hasDerivAt
    (IsingModel.latticeGraph d) Λ ht n

end Ambient
end IsingModel
