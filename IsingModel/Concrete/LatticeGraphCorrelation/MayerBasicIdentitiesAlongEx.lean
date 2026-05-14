import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities

/-!
# Concrete AlongExhaustion Mayer basic identity wrappers

Narrow child module for eight ℤ^d `*AlongExhaustion_latticeGraph_*`
Mayer basic identity wrappers (vdPolymerFamilies_sum / mayerPartialSum /
mayerExpansionTerm at zero / one / `_at_zero`). Each wrapper is a thin
pass-through to the corresponding ambient `*AlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum at t = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_at_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))).card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_at_one
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum at N = 1**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        t ^ P.card :=
  Ambient.mayerPartialSumAlongExhaustion_one
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N 0 = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ N n

/-! ## Moved: mayerExpansionTermAlongExhaustion_latticeGraph wrappers

The three wrappers
`mayerExpansionTermAlongExhaustion_latticeGraph_zero`,
`mayerExpansionTermAlongExhaustion_latticeGraph_one`,
`mayerExpansionTermAlongExhaustion_latticeGraph_at_zero`
now live in `MayerBasicIdentitiesAlongExMayerExpansionTerm.lean`. -/


end Ambient
end IsingModel
