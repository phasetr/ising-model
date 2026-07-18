import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer basic identity wrappers along an exhaustion

Basic along-exhaustion identity wrappers for `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum`. Each wrapper is a
thin pass-through to the corresponding Λ-level lemma. This module
gathers the eight small-`k` / at-zero / at-one forwarders that callers
need without pulling in the monolithic original special-cases module:

* `mayerPartialSumAlongExhaustion_zero` / `_one` / `_at_zero`
* `mayerExpansionTermAlongExhaustion_zero` / `_one` / `_at_zero`
* `vdPolymerFamilies_sumAlongExhaustion_at_zero` / `_at_one`
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 basic identities at_zero / at_one along-ex wraps -/

/-- **Along-ex: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerPartialSum_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSumAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerPartialSum_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N 0 = 0 :=
  mayerPartialSum_Λ_at_zero G (Λ.volume n) N

/-- **Along-ex: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 0 t = 0 :=
  mayerExpansionTerm_Λ_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTermAlongExhaustion_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t =
      ∑ P ∈ IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)), t ^ P.card :=
  mayerExpansionTerm_Λ_one G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTermAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) k 0 = 0 :=
  mayerExpansionTerm_Λ_at_zero G (Λ.volume n) k

/-- **Along-ex: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  vdPolymerFamilies_sum_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  vdPolymerFamilies_sum_Λ_at_one G (Λ.volume n)

end Ambient
end IsingModel
