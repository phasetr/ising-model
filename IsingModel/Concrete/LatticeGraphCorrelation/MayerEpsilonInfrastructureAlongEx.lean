import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure

/-!
# ℤ^d AlongExhaustion mayer-epsilon infrastructure wrappers

Narrow child module for six ℤ^d AlongExhaustion mayer-epsilon
infrastructure wrappers extracted from `MayerEpsilonInfrastructure.lean`:

* `mayerExpansionTermAlongExhaustion_latticeGraph_one_nonneg_of_nonneg`,
* `mayerExpansionTermAlongExhaustion_latticeGraph_two_nonpos_of_nonneg`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_at_zero`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_continuous`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_lt_one_eventually`,
* `allPolymersAlongExhaustion_latticeGraph_eq_empty_of_edgeFinset_empty`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: 0 ≤ mayerExpansionTerm at n = 1** under
`0 ≤ t`. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 1 t :=
  Ambient.mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: mayerExpansionTerm at n = 2 ≤ 0** under
`0 ≤ t`. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_two_nonpos_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) 2 t
      ≤ 0 :=
  Ambient.mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: ε(0) = 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) is `Continuous`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_lt_one_eventually
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem
allPolymersAlongExhaustion_latticeGraph_eq_empty_of_edgeFinset_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅ :=
  Ambient.allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (IsingModel.latticeGraph d) Λ n h_empty

end Ambient
end IsingModel
