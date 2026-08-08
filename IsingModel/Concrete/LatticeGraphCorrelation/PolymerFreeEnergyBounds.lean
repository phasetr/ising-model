import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds
import IsingModel.Lattice

/-!
# ℤ^d Λ polymerFreeEnergy sign, upper bounds and monotonicity (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the elementary envelope of
the polymer free energy: nonnegativity and the ceilings `|E| * log (1 + t)` and `|E| * t` for
`0 ≤ t`, together with monotonicity on `Set.Ici 0`. These are the ℤ^d bounds that keep the
GJ §18.5 cluster expansion under control in the activity variable.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
