import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure

/-!
# Concrete Mayer epsilon infrastructure wrappers

Narrow child module for concrete `ℤ^d` epsilon infrastructure wrappers,
the first Mayer-term sign wrappers, and the edgeless `allPolymers` wrapper.
This keeps callers that only need these forwarders out of the monolithic
lattice-correlation legacy module.
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

/-- **ℤ^d Λ: ε(0) = 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_at_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_continuous
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_lt_one_eventually
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually
    (IsingModel.latticeGraph d) Λ

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
