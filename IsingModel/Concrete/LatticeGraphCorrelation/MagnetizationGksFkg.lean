import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d non-negative correlations of Gibbs-type weights

Concrete statements on the subgraph induced by a fixed finite volume of `Fin d → ℤ`, to the
effect that certain weights on the configuration space have non-negative correlations. A
product of exponentials of couplings times spin products, indexed by an arbitrary family of
vertex sets, has the property once every coupling in that family is non-negative; the product
of edge and site exponentials has it once the edge weights are non-negative on the induced
edge set and the site weights are non-negative at every vertex. For a parameter record
satisfying `Ferromagnetic`, the Boltzmann weight itself has the property, and the
unnormalized Gibbs expectation of the spin product of a finite set of vertices is
non-negative. No instance argument is taken.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d hasNonnegCorrelations_general_coupling direct** (Λ-induced):
general non-negative couplings give HNC product. -/
theorem hasNonnegCorrelations_general_coupling_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (couplings : Finset (Finset (↑Λ : Type _)))
    (K : Finset (↑Λ : Type _) → ℝ)
    (hK : ∀ C ∈ couplings, 0 ≤ K C) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ C ∈ couplings, Real.exp (K C * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_general_coupling couplings K hK

/-- **ℤ^d hasNonnegCorrelations_edge_site_product direct** (Λ-induced):
the edge × site product weight has HNC on `Config ↑Λ`. -/
theorem hasNonnegCorrelations_edge_site_product_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (edgeK : Sym2 (↑Λ : Type _) → ℝ) (siteK : (↑Λ : Type _) → ℝ)
    (hedgeK : ∀ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
      0 ≤ edgeK e)
    (hsiteK : ∀ i, 0 ≤ siteK i) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      (∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Real.exp (edgeK e * IsingModel.edgeSpin (K := ℝ) σ e)) *
      (∏ i : (↑Λ : Type _),
        Real.exp (siteK i * IsingModel.Spin.sign ℝ (σ i))) :=
  IsingModel.hasNonnegCorrelations_edge_site_product
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) edgeK siteK hedgeK hsiteK

/-- **ℤ^d GKS numerator nonneg** at Λ-induced: for ferromagnetic `p`,
`0 ≤ numerator (spinProduct A)`. -/
theorem gks_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    0 ≤ IsingModel.numerator
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
          (IsingModel.spinProduct A) :=
  IsingModel.gks_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A

/-- **ℤ^d boltzmannWeight has non-negative correlations** at Λ-induced
(ferromagnetic). -/
theorem boltzmannWeight_hasNonnegCorrelations_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.HasNonnegCorrelations (IsingModel.boltzmannWeight
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.boltzmannWeight_hasNonnegCorrelations
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

end Ambient

end IsingModel
