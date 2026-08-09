import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Factorization

/-!
# ℤ^d Friedli-Velenik factorisation of the Boltzmann weight

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the per-configuration factorisation used to write the complex
partition function as a Lee-Yang polynomial: the product of the edge exponentials splits into
an edge-count prefactor times a product of `edgeWeight` values, the evaluation of
`isingEdgePoly` at the subset associated with a configuration is exactly that product, and
the exponentiated negative Hamiltonian equals `leeYangNormalization` times that polynomial
value times the product of `leeYangFugacityVec` over the configuration's subset. No statement
here carries a hypothesis; the real parameters, the edge activity and the complex field are
unconstrained.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d edge-term product factorisation** (Λ-induced):
`∏_e exp(β·J·edgeSpin σ e) = exp(β·J·|E|) · ∏_e edgeWeight … (configToFinset σ)`.
Helper for the Friedli-Velenik factorisation of Z_ℂ. -/
theorem prod_exp_beta_J_edgeSpin_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    ∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Complex.exp ((β : ℂ) * (J : ℂ) * IsingModel.edgeSpinComplex σ e)
      = Complex.exp ((β : ℂ) * (J : ℂ) *
            ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
              : ℂ))
        * ∏ e ∈
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
              IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2
                (Real.exp (-2 * β * J)) (IsingModel.configToFinset σ) :=
  IsingModel.prod_exp_beta_J_edgeSpin_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J σ

/-- **ℤ^d `isingEdgePoly` evaluated at `configToFinset σ`** (Λ-induced):
product over edges of `edgeWeight`. -/
theorem isingEdgePoly_apply_configToFinset_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)
        (IsingModel.configToFinset σ)
      = ∏ e ∈
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            IsingModel.edgeWeight (Quot.out e).1 (Quot.out e).2 t
              (IsingModel.configToFinset σ) :=
  IsingModel.isingEdgePoly_apply_configToFinset
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t σ

/-- **ℤ^d per-configuration Friedli-Velenik factorisation** (Λ-induced):
`exp(-β · H(σ)) = leeYangNormalization · isingEdgePoly · ∏ fugacityVec`. -/
theorem exp_neg_beta_hamiltonian_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h σ)
      = IsingModel.leeYangNormalization (β : ℂ) (J : ℂ) h
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          (Fintype.card (↑Λ : Type _))
        * IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (Real.exp (-2 * β * J)))
            (IsingModel.configToFinset σ)
        * ∏ i ∈ IsingModel.configToFinset σ,
            IsingModel.leeYangFugacityVec (β : ℂ) h i :=
  IsingModel.exp_neg_beta_hamiltonian_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h σ

end Ambient

end IsingModel
