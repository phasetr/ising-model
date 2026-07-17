import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# Concrete Mayer epsilon infrastructure wrappers

Narrow child module for concrete `ℤ^d` epsilon infrastructure wrappers,
the first Mayer-term sign wrappers, and the edgeless `allPolymers` wrapper.
This keeps callers that only need these forwarders out of the monolithic
lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty ℤ^d wraps -/

/-- **ℤ^d Λ: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_latticeGraph_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t :=
  Ambient.mayerExpansionTerm_Λ_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two_nonpos_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t ≤ 0 :=
  Ambient.mayerExpansionTerm_Λ_two_nonpos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-! ## Moved: Λ-direct ε(t) infrastructure wrappers

The three `vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_*` wrappers
(`_at_zero`, `_continuous`, `_lt_one_eventually`) now live in
`MayerEpsilonInfrastructureVdSum.lean`. -/



/-- **ℤ^d Λ: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymers_Λ_latticeGraph_eq_empty_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset
      = ∅) :
    IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.allPolymers_Λ_eq_empty_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty

/-! ## Moved: AlongExhaustion mayer-epsilon infrastructure wrappers

The six AlongExhaustion `mayer*AlongExhaustion_latticeGraph_*` /
`vdPolymerFamilies_sumAlongExhaustion_*` /
`allPolymersAlongExhaustion_*` infrastructure wrappers now live in
`MayerEpsilonInfrastructureAlongEx.lean`. -/



end Ambient
end IsingModel
