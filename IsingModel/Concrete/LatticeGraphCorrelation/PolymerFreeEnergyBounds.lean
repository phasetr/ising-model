import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.Lattice

/-!
# Concrete polymer free-energy bound wrappers for the lattice graph

Narrow child module for ℤ^d `polymerFreeEnergy` regularity, bounds,
comparison, and edge-case wrappers. This keeps callers that only need these
forwarders out of the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: ℤ^d polymerFreeEnergy regularity wrappers

The 8 ℤ^d `polymerFreeEnergy_Λ_latticeGraph_*` and
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` regularity wrappers
(`continuousAt`, `differentiableAt`, `continuousOn_Ici_zero`,
`differentiableOn_Ici_zero` in both Λ and AlongExhaustion forms) now
live in
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBoundsRegularity`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ### §18.5 polymerFreeEnergy bound family ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy ≥ 0 under t ≥ 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t :=
  Ambient.polymerFreeEnergy_Λ_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: polymerFreeEnergy ≤ |E| · log(1+t) under t ≥ 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_card_log_one_plus_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
        Real.log (1 + t) :=
  Ambient.polymerFreeEnergy_Λ_le_card_log_one_plus_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: polymerFreeEnergy ≤ |E| · t under t ≥ 0**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_card_mul_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card * t :=
  Ambient.polymerFreeEnergy_Λ_le_card_mul_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: polymerFreeEnergy MonotoneOn (Set.Ici 0)**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    MonotoneOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-! ## Moved: ℤ^d along-exhaustion polymerFreeEnergy bound wrappers

The four wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_nonneg_of_nonneg`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_one_plus_of_nonneg`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_mul_of_nonneg`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_monotoneOn_Ici_zero` now
live in `PolymerFreeEnergyBoundsAlongEx.lean`. -/


/-! ## Moved: Λ polymerFreeEnergy edge-case / comparison wrappers

The four `polymerFreeEnergy_Λ_latticeGraph_*` edge-case / comparison
wrappers (`eq_zero_of_no_polymers`, `eq_zero_of_edgeFinset_empty`,
`le_of_le_of_nonneg`, `le_of_le_strict_form`) now live in
`PolymerFreeEnergyBoundsLambdaEdgeCases.lean`. -/



/-! ## Moved: AlongExhaustion polymerFreeEnergy eq_zero / le wrappers

The four wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` (`eq_zero_of_no_polymers`,
`eq_zero_of_edgeFinset_empty`, `le_of_le_of_nonneg`,
`le_of_le_strict_form`) now live in
`PolymerFreeEnergyBoundsAlongExZeroLe.lean`. -/

/-! ## Moved: ℤ^d polymerFreeEnergy tanh-bound wrappers

The 8 ℤ^d polymerFreeEnergy tanh-bound wrappers
(`polymerFreeEnergy_Λ_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBoundsTanh`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
