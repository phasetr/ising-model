import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.DomainGeometry

/-!
# ℤ^d positive real part, a normalised log-branch, and a polynomial expansion

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` unrelated steps of the Lee-Yang argument, each with its own
hypotheses. The real part of the exponentiated negative Hamiltonian is positive at every
configuration, under `0 < β` together with the subdomain bound `β * |Im h| * |Λ| < π / 2`. A
logarithm of the partition function normalised at the centre of a ball exists whenever that
ball lies in `leeYangDomain`, under `0 < β` and `0 < J`, with no positivity assumed of the
radius. Non-vanishing of the partition function is restated as membership in the set of
non-zero complex numbers, assuming exactly that non-vanishing. Finally `isingEdgePoly`
evaluated at `leeYangFugacityVec` is expanded as a sum over subsets of the vertex type, with
no hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Re(exp(-β · H(σ))) > 0` on Lee-Yang subdomain** (Λ-induced):
per-configuration positive-real-part. Helper for
`partitionFunctionComplex_re_pos_of_leeYangSubdomain`. -/
theorem exp_neg_beta_hamiltonian_re_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < (Complex.exp (-(β : ℂ) * IsingModel.hamiltonianComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h σ)).re :=
  IsingModel.exp_neg_beta_hamiltonian_re_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ σ

/-- **ℤ^d normalised local log-branch of `Z` on a ball in `leeYangDomain`**
(Λ-induced, ferromagnetic). Intermediate between
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph` and
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`. -/
theorem exists_normalised_logZ_branch_on_ball_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} {r : ℝ}
    (hsub : Metric.ball h₀ r ⊆ IsingModel.leeYangDomain) :
    ∃ g : ℂ → ℂ, g h₀ = Complex.log
        (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ))
      ∧ ∀ z ∈ Metric.ball h₀ r, HasDerivAt g
          (deriv (fun h'' => IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (J : ℂ) h'' (β : ℂ)) z
            / IsingModel.partitionFunctionComplex
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (J : ℂ) z (β : ℂ)) z :=
  IsingModel.exists_normalised_logZ_branch_on_ball
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hsub

/-- **ℤ^d `Z_ℂ ≠ 0 → Z_ℂ ∈ {z ≠ 0}`** (Λ-induced): non-vanishing
restatement (trivial but useful set-level restatement). -/
theorem partitionFunctionComplex_ne_zero_not_iff_slitPlane_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) (h : ℂ)
    (hne : IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β ≠ 0) :
    IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ ({z : ℂ | z ≠ 0}) :=
  IsingModel.partitionFunctionComplex_ne_zero_not_iff_slitPlane
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h hne

/-- **ℤ^d product-form for `isingEdgePoly` evaluated at `leeYangFugacityVec`**
(Λ-induced): expands `P_E(z(h))` over `Finset ι` subsets. -/
theorem isingEdgePoly_eval_leeYangFugacityVec_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (t : ℝ) (β h : ℂ) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec β h)
      = ∑ X : Finset (↑Λ : Type _),
          ((IsingModel.graphToEdgeList
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t).map
              fun e => IsingModel.edgeWeight e.1 e.2.1 e.2.2 X).prod *
            ∏ _i ∈ X, IsingModel.leeYangFugacity β h :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t β h

end Ambient

end IsingModel
