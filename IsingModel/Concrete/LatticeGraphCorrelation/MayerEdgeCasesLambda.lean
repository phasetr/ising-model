import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# ℤ^d Mayer identity at the trivial activity slices, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the Mayer identity
in unfolded form — the logarithm of the activity sum over the vertex-disjoint compatible
polymer families of the induced subgraph equals the Mayer partial sum at every truncation
order — at the activity slices where each side is trivial: at the bare activity `0`, and at
the activity `tanh (β * J)` under `β * J = 0`, at `β = 0`, and at `J = 0`. The bare-activity
statement assumes nothing about the parameters; the statement at a general parameter pair
assumes `β * J = 0`; the remaining ones substitute `0` for `β` and for `J` literally and leave
the other parameter arbitrary.
-/

namespace IsingModel
namespace Ambient

open Finset Real

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
