import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# ℤ^d Λ-direct Mayer identity edge-case wrappers

Narrow child module for four ℤ^d Λ-direct
`mayer_identity_at_*_Λ_latticeGraph` wrappers extracted from
`MayerEdgeCases.lean`:

* `mayer_identity_at_zero_Λ_latticeGraph`,
* `mayer_identity_at_betaJ_zero_Λ_latticeGraph`,
* `mayer_identity_at_beta_zero_Λ_latticeGraph`,
* `mayer_identity_at_J_zero_Λ_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 mayer_identity_at edge-case ℤ^d wraps -/

/-- **ℤ^d Λ: Mayer identity at `t = 0`**. -/
theorem mayer_identity_at_zero_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N 0 :=
  Ambient.mayer_identity_at_zero_Λ (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: Mayer identity at `β·J = 0`**. -/
theorem mayer_identity_at_betaJ_zero_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_at_betaJ_zero_Λ
    (IsingModel.latticeGraph d) Λ hβJ N

/-- **ℤ^d Λ: Mayer identity at `β = 0`**. -/
theorem mayer_identity_at_beta_zero_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  Ambient.mayer_identity_at_beta_zero_Λ
    (IsingModel.latticeGraph d) Λ J N

/-- **ℤ^d Λ: Mayer identity at `J = 0`**. -/
theorem mayer_identity_at_J_zero_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph (IsingModel.latticeGraph d) Λ),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  Ambient.mayer_identity_at_J_zero_Λ
    (IsingModel.latticeGraph d) Λ β N

end Ambient
end IsingModel
