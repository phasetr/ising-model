import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionClosedForms
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperComplete
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperCompleteFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwich
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationContinuity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrict
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviationStrictFerro
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBound
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBound
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDecayCapstones
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasic
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPair
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelation

/-!
# The zero-field free-energy sandwich and the odd-set numerator, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `|E|` for the edge count of the stage subgraph and `|Λ|` for the cardinality of the
stage volume.

Under `0 ≤ β * J` and `0 < |Λ|`, the free energy at the parameter record `⟨J, 0, β⟩` lies
between `Real.log 2 + (|E| / |Λ|) * Real.log (Real.cosh (β * J))` and
`Real.log 2 + (|E| / |Λ|) * Real.log (2 * Real.cosh (β * J))`.

Separately, for a site set `A` of the stage volume of odd cardinality, the finset of subsets
`X` of the stage edge finset whose degree at every site is even off `A` and odd on `A` is
empty. Beyond the ambient data, that statement takes only the stage index `n`, the site set
`A`, and the hypothesis `Odd A.card`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion freeEnergy high-temp sandwich (FV (3.45))**: under
`0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`log 2 + (|E_n|/|Λ_n|) log cosh(βJ) ≤ f_n ≤ log 2 + (|E_n|/|Λ_n|) log(2·cosh βJ)`. -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound G Λ J β hβJ n hne,
   freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound G Λ J β hβJ n hne⟩

/-- **Along-exhaustion FV (3.46) numerator filter empty for odd `|A|`**:
at every stage `n`, for any `A : Finset ↑(Λ.volume n)` of odd cardinality,
the FV (3.46) numerator filter set is *literally empty*.
Per-stage application of `high_temp_numerator_filter_eq_empty_of_odd_card_Λ`
(Step 299), via the edge-vertex handshake. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (A : Finset ↑(Λ.volume n)) (hA_odd : Odd A.card) :
    (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_Λ G (Λ.volume n) A hA_odd

end Ambient
end IsingModel
