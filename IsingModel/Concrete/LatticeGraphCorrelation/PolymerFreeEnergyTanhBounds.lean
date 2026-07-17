import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Concrete polymer free-energy tanh-bound wrappers

Narrow child module for concrete `ℤ^d` `polymerFreeEnergy` tanh bounds,
ferromagnetic bounds, the `log(1 + eps)` decomposition, and the `HasDerivAt`
wrapper. This keeps callers that only need these forwarders out of the
monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy tanh ≤ |E| · tanh** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.tanh (β * J) :=
  Ambient.polymerFreeEnergy_Λ_tanh_le_card_mul
    (IsingModel.latticeGraph d) Λ hβJ

/-! ## Moved: ferromagnetic tanh-bound wrappers

The three ferromagnetic Λ-layer wrappers
`polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_mul_ferro`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_sandwich_ferro`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_le_card_log_two_ferro` now
live in `PolymerFreeEnergyTanhBoundsFerro.lean`. -/


/-- **ℤ^d Λ: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_log_one_add_eps
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.polymerFreeEnergy_Λ_eq_log_one_add_eps
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasDerivAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  Ambient.polymerFreeEnergy_Λ_hasDerivAt
    (IsingModel.latticeGraph d) Λ ht

/-! ## Moved: AlongExhaustion polymerFreeEnergy tanh-bound wrappers

The six AlongExhaustion `polymerFreeEnergyAlongExhaustion_latticeGraph_*`
wrappers (tanh bounds, ferro variants, log_one_add_eps, hasDerivAt) now
live in `PolymerFreeEnergyTanhBoundsAlongEx.lean`. -/



end Ambient
end IsingModel
