import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTerm
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhDifferentiable

/-!
# `mayerPartialSum` tanh regularity wrappers along an exhaustion

Records regularity of the along-exhaustion Mayer partial sums in the `tanh`-composed
parameters `β` and `J` (GJ §18.5–§18.6), the input for differentiating the cluster expansion
stagewise. Each is a pass-through of the corresponding `mayerPartialSum_Λ_tanh_*` lemma.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 mayerPartialSum tanh β/J along-ex wraps -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_continuous_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_continuous_J G (Λ.volume n) N β

end Ambient
end IsingModel
