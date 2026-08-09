import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerFilterConnected

/-!
# ℤ^d powers of the nonempty-family activity sum and connected polymer sequences

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the expansion of an arbitrary power of the activity sum over the vertex-disjoint
compatible polymer families of the stage-`n` induced subgraph other than the empty one as a
sum over sequences of such families, together with the description of the polymer sequences of
that subgraph whose incompatibility graph is `Connected`: at length `0` there are none, at
length `1` they are all of them, and at length `2` they are exactly the incompatible pairs. No
condition on the activity or on the exponent is imposed.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: ε(t)^n as multi-Γ piFinset sum**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (k : ℕ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ k =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume n))).erase ∅),
        ∏ i : Fin k, ∏ P ∈ ω i, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pow
    (IsingModel.latticeGraph d) Λ t k n

/-- **ℤ^d along-ex: mayerExpansionTerm filter-connected at k=0 =
∅**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_filter_connected_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  Ambient.mayerExpansionTermAlongExhaustion_filter_connected_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm filter-connected at k=1 = full
piFinset**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_filter_connected_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))) :=
  Ambient.mayerExpansionTermAlongExhaustion_filter_connected_one
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: filter-connected = filter-incompatible at k=2**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_two_filter_conn_eq_incompat
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  Ambient.mayerExpansionTermAlongExhaustion_two_filter_connected_eq_incompat
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
