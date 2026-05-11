import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds

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

/-- **ℤ^d along-exhaustion correlation high-temperature closed form (FV §3.7.3 eq. (3.46))**:
at every stage `n` with `A ⊆ Λ.volume n`, FV (3.46) closed form holds
on the lifted Finset. When `A ⊄`, equals `0`.
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

/-- **ℤ^d along-exhaustion FV (3.46) numerator filter empty for odd `|A|`**:
at every stage `n`, the FV (3.46) numerator filter is empty for any
`A : Finset ↑(Λ.volume n)` of odd cardinality. ℤ^d wrapper of
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

/-- **ℤ^d along-exhaustion FV (3.46) at A = ∅ consistency check**:
under `0 ≤ β·J`,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ ∅ n = 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_empty_A
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset (Fin d → ℤ)) n = 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_empty_A
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j} n`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex singleton ferromagnetic vanish**. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i n

/-- **ℤ^d along-ex pair ferromagnetic sandwich at h = 0**: under
`0 ≤ J, 0 < β`, `0 ≤ ⟨σ_i σ_j⟩^Λ_n ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j n

/-- **ℤ^d along-ex singleton sandwich at h = 0**: `= 0 ∧ ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_eq_zero_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-ex pair correlation ≤ 1 at h = 0**. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one
    (IsingModel.latticeGraph d) Λ J β i j n

/-- **ℤ^d along-ex pair sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n ≤ 1`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex pair+singleton bundle at h = 0**: combines
`{i}`-vanishing with the `{i,j}` sandwich at every stage `n`. ℤ^d
wrapper of `correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and
`⟨σ_iσ_j⟩ ≤ 1` at every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j n

/-- **ℤ^d along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

/-- **ℤ^d along-ex pair + singleton trivial-slices full bundle at
h = 0**: at `J = 0` and `β = 0`, both pair and singleton ℤ^d
along-exhaustion correlations vanish at every stage `n`. ℤ^d wrapper. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (IsingModel.latticeGraph d) Λ J β i j n

/-- **ℤ^d along-ex pair correlation single-edge tanh lower bound at stage `n`
(GJ §18.3 / FV (3.46))**:
applies the Λ-level single-edge lower bound at the stage-`n` subtype.
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

/-- **ℤ^d along-ex pair correlation strict positivity under edge at stage `n`**:
under `0 < β·J` and an edge in the stage-`n` induced ℤ^d subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge
    (IsingModel.latticeGraph d) Λ J β hβJ n i j hij he

/-- **ℤ^d along-ex ferromagnetic pair single-edge tanh lower bound at stage `n`**:
under `0 ≤ J, 0 < β` and an edge in the stage-`n` induced ℤ^d subgraph,
`⟨σ_iσ_j⟩^{Λ_n} ≥ tanh(β·J) / 2^|E_{Λ_n}|`. ℤ^d wrapper. -/
theorem
    correlationAlongExhaustion_latticeGraph_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n i j hij he

/-- **ℤ^d along-ex ferromagnetic pair strict positivity under edge at stage `n`**:
under `0 < J, 0 < β` and an edge in the stage-`n` induced ℤ^d subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. ℤ^d wrapper. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n i j hij he

/-- **ℤ^d along-ex pair at J=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero
    (IsingModel.latticeGraph d) Λ β i j n

/-- **ℤ^d along-ex pair at β=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero
    (IsingModel.latticeGraph d) Λ J i j n

/-- **ℤ^d along-ex singleton at J=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero
    (IsingModel.latticeGraph d) Λ β i n

/-- **ℤ^d along-ex singleton at β=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero
    (IsingModel.latticeGraph d) Λ J i n

/-- **ℤ^d along-exhaustion magnetization vanishes at h = 0**: at every
stage `n`,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ {i} n = 0`
for any ambient site `i : Fin d → ℤ`. ℤ^d wrapper. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-exhaustion Z₂ symmetry of correlation at h = 0**:
for ambient `A : Finset (Fin d → ℤ)` of odd cardinality,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ A n = 0` at
every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_odd_card_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (Fin d → ℤ)) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (IsingModel.latticeGraph d) Λ J β A hA_odd n

end Ambient

end IsingModel
