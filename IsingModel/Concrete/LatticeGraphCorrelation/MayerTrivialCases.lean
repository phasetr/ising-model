import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Concrete Mayer trivial-case wrappers

Narrow child module for concrete `ℤ^d` `mayerPartialSum 0 ≤ polymerFreeEnergy`
comparisons and Mayer identity wrappers for no-polymer, trivial, and edgeless
cases. This keeps callers that only need these wrappers out of the monolithic
lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t :=
  Ambient.mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem
mayerPartialSum_zero_Λ_latticeGraph_tanh_le_polymerFreeEnergy_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) :=
  Ambient.mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-! ## Moved: AlongExhaustion mayerPartialSum_zero wrappers

The three `mayerPartialSum_zero_AlongExhaustion_latticeGraph_*` wrappers
(plain, tanh, ferro variants) now live in `MayerTrivialCasesAlongEx.lean`. -/



/-! ## Moved: Λ-layer Mayer identity trivial-case wrappers

The five wrappers
`mayer_identity_of_no_polymers_Λ_latticeGraph`,
`mayer_identity_of_no_polymers_tanh_Λ_latticeGraph`,
`mayer_identity_of_trivial_Λ_latticeGraph`,
`mayer_identity_of_edgeFinset_empty_Λ_latticeGraph`,
`mayer_identity_of_edgeFinset_empty_tanh_Λ_latticeGraph` now live in
`MayerTrivialCasesLambdaIdentity.lean`. -/


end Ambient
end IsingModel
