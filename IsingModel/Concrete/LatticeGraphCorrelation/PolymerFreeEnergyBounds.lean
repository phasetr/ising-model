import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds

/-!
# Concrete polymer free-energy bound wrappers for the lattice graph

Narrow child module for ℤ^d `polymerFreeEnergy` regularity, bounds,
comparison, and edge-case wrappers. This keeps callers that only need these
forwarders out of the monolithic concrete legacy module.
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
The legacy import path is preserved by re-importing the new child.
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

/-- **ℤ^d along-ex: polymerFreeEnergy ≥ 0 under t ≥ 0**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy ≤ |E| · log(1+t) under t ≥ 0**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_log_one_plus_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card *
        Real.log (1 + t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_card_log_one_plus_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy ≤ |E| · t under t ≥ 0**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_le_card_mul_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card * t :=
  Ambient.polymerFreeEnergyAlongExhaustion_le_card_mul_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy MonotoneOn (Set.Ici 0)**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n

/-! ### §18.5 polymerFreeEnergy edge-case + comparison ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy = 0 for empty-polymer induced graphs**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t = 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ h_no t

/-- **ℤ^d Λ: polymerFreeEnergy = 0 for edgeless induced graphs**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph
      (IsingModel.latticeGraph d) Λ).edgeFinset = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t = 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty t

/-- **ℤ^d Λ: polymerFreeEnergy preserves order on `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_of_le_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s :=
  Ambient.polymerFreeEnergy_Λ_le_of_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht hs hts

/-- **ℤ^d Λ: polymerFreeEnergy strict-form order preservation**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_le_of_le_strict_form
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) s :=
  Ambient.polymerFreeEnergy_Λ_le_of_le_strict_form
    (IsingModel.latticeGraph d) Λ ht hts

/-! ## Moved: AlongExhaustion polymerFreeEnergy eq_zero / le wrappers

The four wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_{eq_zero_of_no_polymers,eq_zero_of_edgeFinset_empty,le_of_le_of_nonneg,le_of_le_strict_form}`
now live in `PolymerFreeEnergyBoundsAlongExZeroLe.lean`. -/

/-! ## Moved: ℤ^d polymerFreeEnergy tanh-bound wrappers

The 8 ℤ^d polymerFreeEnergy tanh-bound wrappers
(`polymerFreeEnergy_Λ_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`
and `polymerFreeEnergyAlongExhaustion_latticeGraph_{tanh_sandwich,
le_card_log_two_of_le_one, tanh_le_card_log_two, tanh_double_bound}`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBoundsTanh`.
The legacy import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
