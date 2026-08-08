import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening

/-!
# ℤ^d AlongExhaustion cluster-expansion ε(t) sharpening wrappers

Instantiates the sign and vanishing facts about the along-exhaustion cluster-expansion
remainder `ε(t) = vdPolymerFamilies_sum − 1` at `IsingModel.latticeGraph d`, which is what
sharpens the GJ §18.5 polymer free-energy bounds.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hk n

end Ambient
end IsingModel
