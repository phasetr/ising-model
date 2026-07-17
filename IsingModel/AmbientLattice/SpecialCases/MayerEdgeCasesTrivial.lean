import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Mayer trivial-slice edge-case wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion Mayer
identity wrappers at the trivial parameter slices
`β = 0` and `J = 0` extracted from `MayerEdgeCases.lean`:

* `mayer_identity_at_beta_zero_AlongExhaustion`
* `mayer_identity_at_J_zero_AlongExhaustion`

Each wrapper is a thin pass-through to the corresponding
`mayer_identity_at_*_zero_Λ` ambient lemma. Theorem names are
unchanged from the former `MayerEdgeCases` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: Mayer identity at `β = 0`**. -/
theorem mayer_identity_at_beta_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_beta_zero_Λ G (Λ.volume n) J N

/-- **Along-ex: Mayer identity at `J = 0`**. -/
theorem mayer_identity_at_J_zero_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n)),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_J_zero_Λ G (Λ.volume n) β N

end Ambient
end IsingModel
