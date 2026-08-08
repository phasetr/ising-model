import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTermDifferentiable

/-!
# `mayerExpansionTerm` tanh `Continuous` wrappers along an exhaustion

Records continuity of the individual along-exhaustion Mayer expansion terms in the
`tanh`-composed parameters `β` and `J` (GJ §18.5), one wrapper varying `β` at fixed `J` and
the other varying `J` at fixed `β`. Each passes through to its
`mayerExpansionTerm_Λ_tanh_continuous_*` ambient counterpart. The matching
`mayerExpansionTermAlongExhaustion_tanh_differentiable_*` statements are not proved here; they
reach importers of this module through its imports.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayerExpansionTerm tanh β/J along-ex wraps -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_continuous_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_continuous_J G (Λ.volume n) k β

end Ambient
end IsingModel
