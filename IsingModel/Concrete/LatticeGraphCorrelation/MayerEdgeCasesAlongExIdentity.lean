import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases

/-!
# Concrete along-ex Mayer identity edge-case wrappers

Narrow child module for four ℤ^d
`mayer_identity_at_{zero,betaJ_zero,beta_zero,J_zero}_AlongExhaustion_latticeGraph`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `mayer_identity_at_*_AlongExhaustion` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: Mayer identity at `t = 0`**. -/
theorem mayer_identity_at_zero_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N 0 :=
  Ambient.mayer_identity_at_zero_AlongExhaustion
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: Mayer identity at `β·J = 0`**. -/
theorem mayer_identity_at_betaJ_zero_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_at_betaJ_zero_AlongExhaustion
    (IsingModel.latticeGraph d) Λ hβJ N n

/-- **ℤ^d along-ex: Mayer identity at `β = 0`**. -/
theorem mayer_identity_at_beta_zero_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.mayer_identity_at_beta_zero_AlongExhaustion
    (IsingModel.latticeGraph d) Λ J N n

/-- **ℤ^d along-ex: Mayer identity at `J = 0`**. -/
theorem mayer_identity_at_J_zero_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.mayer_identity_at_J_zero_AlongExhaustion
    (IsingModel.latticeGraph d) Λ β N n

end Ambient
end IsingModel
