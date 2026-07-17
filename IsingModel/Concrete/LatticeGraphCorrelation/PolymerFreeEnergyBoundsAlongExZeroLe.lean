import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds
import IsingModel.Lattice

/-!
# Concrete AlongExhaustion polymerFreeEnergy eq_zero / le wrappers

Narrow child module for four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_{eq_zero_of_no_polymers,
eq_zero_of_edgeFinset_empty,le_of_le_of_nonneg,le_of_le_strict_form}`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `polymerFreeEnergyAlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
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

/-- **ℤ^d along-ex: polymerFreeEnergy preserves order on `[0, ∞)`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_le_of_le_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_of_le_of_nonneg
    (IsingModel.latticeGraph d) Λ n ht hs hts

/-- **ℤ^d along-ex: polymerFreeEnergy strict-form order
preservation**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_le_of_le_strict_form
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_of_le_strict_form
    (IsingModel.latticeGraph d) Λ n ht hts

end Ambient
end IsingModel
