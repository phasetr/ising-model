import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonneg

/-!
# Polymer free-energy bound wrappers along an exhaustion

Narrow child module for along-exhaustion `polymerFreeEnergy` regularity,
bounds, comparison, and edge-case wrappers. This keeps callers that only need
these forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Moved: polymerFreeEnergyAlongExhaustion regularity wrappers

The four `polymerFreeEnergyAlongExhaustion_*` regularity wrappers
(`continuousAt`, `differentiableAt`, `continuousOn_Ici_zero`,
`differentiableOn_Ici_zero`) now live in
`PolymerFreeEnergyBoundsRegularity.lean`. They are re-imported here
so downstream consumers continue to see the symbols. -/



/-! ## Moved: polymerFreeEnergyAlongExhaustion `_of_nonneg` bound wrappers

The three `polymerFreeEnergyAlongExhaustion_*_of_nonneg` bound wrappers
(`nonneg`, `le_card_log_one_plus`, `le_card_mul`) now live in
`PolymerFreeEnergyBoundsNonneg.lean`. They are re-imported here so
downstream consumers continue to see the symbols. -/



/-- **Along-ex: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) t) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_monotoneOn_Ici_zero G (Λ.volume n)

/-- **Along-ex: `polymerFreeEnergy = 0` for empty-polymer induced
graphs** (§18.5 along-ex wrap of Step 621). -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t

/-- **Along-ex: `polymerFreeEnergy = 0` for edgeless induced
graphs** (§18.5 along-ex wrap of Step 623). -/
theorem
polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t

/-- **Along-ex: `polymerFreeEnergy` preserves order on `[0, ∞)`**
(§18.5 along-ex wrap of Step 649). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_of_nonneg
    G (Λ.volume n) ht hs hts

/-- **Along-ex: `polymerFreeEnergy` strict-form order preservation**
(§18.5 along-ex wrap of Step 650). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_strict_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_strict_form
    G (Λ.volume n) ht hts

/-- **Along-ex: `polymerFreeEnergy` tanh-form sandwich** (§18.5
along-ex wrap of Step 632). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich G (Λ.volume n) hβJ

/-- **Along-ex: `polymerFreeEnergy ≤ |E|·log 2` for `0 ≤ t ≤ 1`**
(§18.5 along-ex wrap of Step 642). -/
theorem polymerFreeEnergyAlongExhaustion_le_card_log_two_of_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_le_card_log_two_of_le_one
    G (Λ.volume n) ht ht1

/-- **Along-ex: `polymerFreeEnergy_tanh ≤ |E|·log 2` under `0 ≤ β·J`**
(§18.5 along-ex wrap of Step 643). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_le_card_log_two G (Λ.volume n) hβJ

/-- **Along-ex: `polymerFreeEnergy_tanh` double bound** (§18.5
along-ex wrap of Step 645). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_double_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_double_bound G (Λ.volume n) hβJ

end Ambient
end IsingModel
