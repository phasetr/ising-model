import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSum

/-!
# Mayer term sign wrappers and edgeless `allPolymers` along an exhaustion

Narrow child module for the first Mayer-term sign wrappers
(`mayerExpansionTerm` at `n = 1`, `n = 2`) and the edgeless
`allPolymers` wrapper along an exhaustion. This keeps callers that
only need these forwarders out of the monolithic legacy special-cases
module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty along-ex wraps -/

/-- **Along-ex: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t :=
  mayerExpansionTerm_Λ_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) 2 t
      ≤ 0 :=
  mayerExpansionTerm_Λ_two_nonpos_of_nonneg G (Λ.volume n) ht

/-! ## Moved: 3 ε(t) infrastructure wrappers

The three `vdPolymerFamilies_sumAlongExhaustion_minus_one_*` ε(t)
infrastructure wrappers (`_at_zero`, `_continuous`,
`_lt_one_eventually`) now live in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSum`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  allPolymers_Λ_eq_empty_of_edgeFinset_empty G (Λ.volume n) h_empty

end Ambient
end IsingModel
