import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# Concrete Mayer basic identity wrappers

Narrow child module for concrete `ℤ^d` at-zero and at-one identities for
`vdPolymerFamilies_sum`, `mayerPartialSum`, and `mayerExpansionTerm`. This
keeps callers that only need these wrappers out of the monolithic
lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 basic identities at_zero / at_one ℤ^d wraps -/

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  Ambient.vdPolymerFamilies_sum_Λ_at_zero (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.vdPolymerFamilies_sum_Λ_at_one (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t = 0 :=
  Ambient.mayerPartialSum_Λ_zero (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at N = 1**. -/
theorem mayerPartialSum_Λ_latticeGraph_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ), t ^ P.card :=
  Ambient.mayerPartialSum_Λ_one (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N 0 = 0 :=
  Ambient.mayerPartialSum_Λ_at_zero (IsingModel.latticeGraph d) Λ N

/-! ## Moved: mayerExpansionTerm_Λ_latticeGraph wrappers

The three wrappers
`mayerExpansionTerm_Λ_latticeGraph_zero`,
`mayerExpansionTerm_Λ_latticeGraph_one`,
`mayerExpansionTerm_Λ_latticeGraph_at_zero` now live in
`MayerBasicIdentitiesMayerExpansionTerm.lean`. -/


/-! ## Moved: AlongExhaustion Mayer basic identity wrappers

The three `mayerExpansionTermAlongExhaustion_latticeGraph_*` Mayer basic
identity wrappers (at `zero` / `one` / `_at_zero`) live in
`MayerBasicIdentitiesAlongExMayerExpansionTerm.lean`. -/


end Ambient
end IsingModel
