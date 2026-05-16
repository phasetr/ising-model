import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer ε(t) infrastructure wrappers along an exhaustion (vdPolymerFamilies sum)

Narrow child module for the three §18.5 ambient alongExhaustion
ε(t) = `vdPolymerFamilies_sum_minus_one` infrastructure wrappers
extracted from `MayerEpsilonInfrastructure.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero`
* `vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous`
* `vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually`

Each wrapper is a thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_minus_one_*` lemma. Theorem names are
unchanged from the former `MayerEpsilonInfrastructure` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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

end Ambient
end IsingModel
