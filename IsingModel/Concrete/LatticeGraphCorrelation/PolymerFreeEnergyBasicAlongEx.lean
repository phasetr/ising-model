import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy basic wrappers

Narrow child module for three ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` basic wrappers
extracted from `PolymerFreeEnergyBasic.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_at_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_at_one`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_sandwich_of_nonneg`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyBasic` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: polymerFreeEnergy at `t = 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_at_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))).card :=
  Ambient.polymerFreeEnergyAlongExhaustion_at_one
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card * Real.log (1 + t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

end Ambient
end IsingModel
