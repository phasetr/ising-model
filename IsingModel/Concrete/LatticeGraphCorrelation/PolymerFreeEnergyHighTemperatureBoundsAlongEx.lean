import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds

/-!
# ℤ^d §18.5 AlongExhaustion `vdPolymerFamilies_sum` high-temperature bounds

Instantiates the along-exhaustion high-temperature bounds and monotonicity of the
vertex-disjoint polymer-family sum at `IsingModel.latticeGraph d`, the convergence input for
the ℤ^d cluster expansion.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdSum sandwich for `t ≥ 0`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_le_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

end Ambient
end IsingModel
