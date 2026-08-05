import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete alongExhaustion correlation/sandwich basic wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete alongExhaustion basic
wrappers on `latticeGraph d` at `h = 0`. 25 theorems for
`correlationAlongExhaustion_latticeGraph` (closed form, nonneg, sandwich,
ferromagnetic, trivial-slice vanishings, pair_sandwich,
pair_singleton_bundle, pair_pos_of_edge, singleton, odd_card_eq_zero)
plus `partitionFunctionAlongExhaustion_latticeGraph` sandwich,
`freeEnergyAlongExhaustion_latticeGraph` sandwich, and the high-temp
numerator filter helper. The two `_of_latticeAdj` along-exhaustion
variants intentionally remain in the parent `HighTemperatureBounds`,
since they directly call the Λ-level `_of_latticeAdj` wrappers (which
also live in the parent). The theorem names are unchanged from the
former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d transport of the project free-boundary high-temperature correlation closed form.**
At every stage `n` with `A ⊆ Λ.volume n`, the arbitrary-observable parity ratio holds on the
lifted Finset. When `A ⊄`, the correlation equals `0`.
ℤ^d wrapper of `correlationAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (Fin d → ℤ)) (n : ℕ) (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A n =
      (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
            Even ((if v ∈ liftFinset A hAn then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlationAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β A n hAn

/-- **ℤ^d transport of the free-boundary odd-cardinality numerator cancellation.**
At every stage `n`, the project parity numerator filter is empty for any
`A : Finset ↑(Λ.volume n)` of odd cardinality. This is the ℤ^d wrapper of
`high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion`. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (n : ℕ) (A : Finset ↑(Λ.volume n)) (hA_odd : Odd A.card) :
    (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_alongExhaustion
    (IsingModel.latticeGraph d) Λ n A hA_odd

/-- **ℤ^d along-exhaustion Z high-temp sandwich**: at every stage `n`,
under `0 ≤ β·J`,
`2^|Λ_n| · cosh^|E_n| ≤ Z_n ≤ 2^(|Λ_n|+|E_n|) · cosh^|E_n|`. ℤ^d wrapper. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ ((Λ.volume n).card +
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) *
          Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion freeEnergy high-temp sandwich**: at every stage `n`,
under `0 ≤ β·J` and `0 < |Λ_n|`,
`log 2 + (|E_n|/|Λ_n|) · log cosh(βJ) ≤ f_n ≤ log 2 + (|E_n|/|Λ_n|) · log(2·cosh βJ)`.
ℤ^d wrapper. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
    ∧ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-! ## Moved: ℤ^d HT AlongExhaustion correlation bound wrappers

The 8 ℤ^d along-exhaustion correlation bound wrappers
(`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_empty_A`,
`_at_pair_nonneg`, `_at_singleton_ferromagnetic`,
`_at_pair_ferromagnetic`, `_at_singleton_eq_zero_le_one`,
`_at_pair_le_one`, `_at_pair_sandwich`, `_at_pair_singleton_bundle`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExBasicCorrelation`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: along-ex pair+singleton bundle wrappers

The three `correlationAlongExhaustion_*_pair_singleton` bundle
wrappers (`bundle_ferromagnetic`, `complete_summary`,
`trivial_slices_bundle`) now live in
`HighTemperatureBoundsAlongExBasicPairSingletonBundles.lean`. -/



/-- **ℤ^d transport of the project-derived pair lower bound at stage `n`.**
Applies the Λ-level single-edge lower bound at the stage-`n` subtype.
ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (IsingModel.latticeGraph d) Λ J β hβJ n i j hij he

/-! ## Moved: AlongExhaustion pair-positivity tail wrappers

The three `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge`,
`correlationAlongExhaustion_latticeGraph_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`,
`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`
wrappers now live in `HighTemperatureBoundsAlongExhaustionBasicPairPositive.lean`. -/



/-! ## Moved: ℤ^d HT AlongExhaustion correlation trivial-slice wrappers

The 6 ℤ^d along-exhaustion correlation trivial-slice / symmetry
wrappers
(`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_J_zero`,
`_at_pair_beta_zero`, `_at_singleton_J_zero`, `_at_singleton_beta_zero`,
`_at_singleton`, `_odd_card_eq_zero`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExBasicTrivial`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
