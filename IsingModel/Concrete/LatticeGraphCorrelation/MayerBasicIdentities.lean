import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities

/-!
# Concrete Mayer basic identity wrappers

Narrow child module for concrete `ℤ^d` at-zero and at-one identities for
`vdPolymerFamilies_sum`, `mayerPartialSum`, and `mayerExpansionTerm`. This
keeps callers that only need these wrappers out of the monolithic
lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 basic identities at_zero / at_one ℤ^d wraps -/

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  Ambient.vdPolymerFamilies_sum_Λ_at_zero (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: vdPolymerFamilies_sum at t = 1**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_at_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) Λ)).card :=
  Ambient.vdPolymerFamilies_sum_Λ_at_one (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t = 0 :=
  Ambient.mayerPartialSum_Λ_zero (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at N = 1**. -/
theorem mayerPartialSum_Λ_latticeGraph_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ), t ^ P.card :=
  Ambient.mayerPartialSum_Λ_one (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N 0 = 0 :=
  Ambient.mayerPartialSum_Λ_at_zero (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 0 t = 0 :=
  Ambient.mayerExpansionTerm_Λ_zero (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at n = 1**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) Λ), t ^ P.card :=
  Ambient.mayerExpansionTerm_Λ_one (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n 0 = 0 :=
  Ambient.mayerExpansionTerm_Λ_at_zero (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum at t = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_at_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))).card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_at_one
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum at N = 1**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        t ^ P.card :=
  Ambient.mayerPartialSumAlongExhaustion_one
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N 0 = 0 :=
  Ambient.mayerPartialSumAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 0 t = 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_zero
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 1**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        t ^ P.card :=
  Ambient.mayerExpansionTermAlongExhaustion_one
    (IsingModel.latticeGraph d) Λ t n

/-- **ℤ^d along-ex: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (k : ℕ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k 0 = 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_at_zero
    (IsingModel.latticeGraph d) Λ k n

end Ambient
end IsingModel
