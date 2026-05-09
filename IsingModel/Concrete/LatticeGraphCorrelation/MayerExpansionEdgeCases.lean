import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases

/-!
# Concrete Mayer expansion edge-case wrappers

Narrow child module for concrete `ℤ^d` Mayer expansion `n = 2`, no-polymer,
edgeless, and absolute-bound wrappers. This keeps callers that only need these
forwarders out of the monolithic lattice-correlation legacy module.
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

/-- **ℤ^d Λ: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSum_Λ_latticeGraph_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 2 t =
      (∑ P ∈ IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d) Λ)) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d) Λ))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerPartialSum_Λ_two (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum = 0 on no-polymer induced graphs**. -/
theorem mayerPartialSum_Λ_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t = 0 :=
  Ambient.mayerPartialSum_Λ_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ h_no t N

/-- **ℤ^d Λ: mayerPartialSum = 0 on edgeless induced graphs**. -/
theorem mayerPartialSum_Λ_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset
      = ∅) (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t = 0 :=
  Ambient.mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ h_empty t N

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

/-- **ℤ^d along-ex: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))) ×ˢ
              (IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTermAlongExhaustion_two
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_two_filter
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume n))) ×ˢ
                (IsingModel.allPolymers
                  (inducedGraph (IsingModel.latticeGraph d)
                    (Λ.volume n)))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerExpansionTermAlongExhaustion_two_filter
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t =
      (∑ P ∈ IsingModel.allPolymers
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
            t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n))) ×ˢ
                  (IsingModel.allPolymers
                    (inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  Ambient.mayerPartialSumAlongExhaustion_two
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum = 0 on no-polymer induced
graphs**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_no_polymers
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_eq_zero_of_no_polymers
    (IsingModel.latticeGraph d) Λ n h_no t N

/-- **ℤ^d along-ex: mayerPartialSum = 0 on edgeless induced
graphs**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_eq_zero_of_edgeFinset_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_eq_zero_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ n h_empty t N

/-- **ℤ^d along-ex: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_abs_le
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (k : ℕ) (t : ℝ) (n : ℕ) :
    |IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin k => IsingModel.allPolymers
                (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n))),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  Ambient.mayerExpansionTermAlongExhaustion_abs_le
    (IsingModel.latticeGraph d) Λ k t n

end Ambient
end IsingModel
