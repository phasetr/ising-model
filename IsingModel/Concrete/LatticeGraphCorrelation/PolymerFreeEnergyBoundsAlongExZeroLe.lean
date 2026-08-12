import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds
import IsingModel.Lattice

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy degenerate stages and order (§18.5)

Instantiates along an exhaustion at `IsingModel.latticeGraph d` the degenerate behaviour of
the polymer free energy — it vanishes identically on a stage whose induced graph carries no
polymer, and likewise on one with no edge — and its preservation of the order `t ≤ s`, once
with both activities assumed nonnegative and once with only the lower one. These fix the
boundary cases of the GJ §18.5 cluster expansion on ℤ^d.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy = 0 for empty-polymer induced
graphs**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)) t = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ n h_no t

/-- **ℤ^d along-ex: polymerFreeEnergy = 0 for edgeless induced
graphs**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)) t = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ n h_empty t

/-- On `ℤ^d` along an exhaustion, polymer free energy preserves order when the smaller
activity is nonnegative. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_le_of_le_of_nonneg_left
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_of_le_of_nonneg_left
    (IsingModel.latticeGraph d) Λ n ht hts

end Ambient
end IsingModel
