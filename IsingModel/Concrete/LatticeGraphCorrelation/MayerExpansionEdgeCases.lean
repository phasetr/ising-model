import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Concrete Mayer expansion edge-case wrappers

Narrow child module for concrete `ℤ^d` Mayer expansion `n = 2`, no-polymer,
edgeless, and absolute-bound wrappers. This keeps callers that only need these
forwarders out of the monolithic lattice-correlation module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le ℤ^d wraps -/

/-- **ℤ^d Λ: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
              (IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d) Λ)),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTerm_Λ_two (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_two_filter
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTerm_Λ_two_filter
    (IsingModel.latticeGraph d) Λ t

/-! ## Moved: mayerPartialSum_Λ edge-case wrappers

The three wrappers
`mayerPartialSum_Λ_latticeGraph_two`,
`mayerPartialSum_Λ_latticeGraph_eq_zero_of_no_polymers`,
`mayerPartialSum_Λ_latticeGraph_eq_zero_of_edgeFinset_empty` now live
in `MayerExpansionEdgeCasesPartialSum.lean`. -/


/-- **ℤ^d Λ: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_abs_le
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    |IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d) Λ)),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  Ambient.mayerExpansionTerm_Λ_abs_le
    (IsingModel.latticeGraph d) Λ n t

/-! ## Moved: AlongExhaustion mayer-expansion edge-case wrappers

The six AlongExhaustion `mayer*AlongExhaustion_latticeGraph_*` edge-case
wrappers now live in `MayerExpansionEdgeCasesAlongEx.lean`. -/



end Ambient
end IsingModel
