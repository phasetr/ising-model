import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Concrete Mayer filter-connected wrappers

Narrow child module for concrete §18.5 Mayer filter-connected and
epsilon-power wrappers on the lattice graph. The theorem names are the same
as the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 Mayer filter-connected + ε^n ℤ^d wraps -/

/-- **ℤ^d Λ: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pow
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pow
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d Λ: mayerExpansionTerm filter-connected at n=0 = ∅**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_filter_connected_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  Ambient.mayerExpansionTerm_Λ_filter_connected_zero
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm filter-connected at n=1 = full
piFinset**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_filter_connected_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ)) :=
  Ambient.mayerExpansionTerm_Λ_filter_connected_one
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: filter-connected = filter-incompatible at n=2**. -/
theorem
mayerExpansionTerm_Λ_latticeGraph_two_filter_connected_eq_incompat
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  Ambient.mayerExpansionTerm_Λ_two_filter_connected_eq_incompat
    (IsingModel.latticeGraph d) Λ

/-! ## Moved: along-exhaustion Mayer filter-connected wrappers

The four along-ex `{vdPolymerFamilies_sumAlongExhaustion_*,
mayerExpansionTermAlongExhaustion_*_filter_connected_*}` wrappers
now live in `MayerFilterConnectedAlongEx.lean`. -/



end Ambient
end IsingModel
