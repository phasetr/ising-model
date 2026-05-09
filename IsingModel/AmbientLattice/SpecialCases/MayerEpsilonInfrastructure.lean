import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer epsilon infrastructure wrappers along an exhaustion

Narrow child module for along-exhaustion epsilon infrastructure wrappers,
the first Mayer-term sign wrappers, and the edgeless `allPolymers` wrapper.
This keeps callers that only need these forwarders out of the monolithic legacy
special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty along-ex wraps -/

/-- **Along-ex: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.mayerExpansionTerm
        (inducedGraph G (Λ.volume n)) 1 t :=
  mayerExpansionTerm_Λ_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTermAlongExhaustion_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G (Λ.volume n)) 2 t
      ≤ 0 :=
  mayerExpansionTerm_Λ_two_nonpos_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0) = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_at_zero G (Λ.volume n)

/-- **Along-ex: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_continuous G (Λ.volume n)

/-- **Along-ex: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually G (Λ.volume n)

/-- **Along-ex: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymersAlongExhaustion_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  allPolymers_Λ_eq_empty_of_edgeFinset_empty G (Λ.volume n) h_empty

end Ambient
end IsingModel
