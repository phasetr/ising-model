import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansion
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationBasic
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDecayCapstones
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharper
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviation
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionBasic
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionExpSharper
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionDeviation
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionTripleRatio
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioLogFe
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsFreeEnergyInfinite

/-!
# Concrete high-temperature expansion and bound wrappers for the lattice graph

Narrow child module for the §18.3-§18.4 high-temperature expansion,
lower/upper bound, sandwich, correlation, and deviation wrappers on
`latticeGraph d`. The theorem names are the same as the former legacy
declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff


/-! ## Moved: high-temperature partition-function and free-energy expansion wrappers

The §18.3-§18.4 high-temperature partition-function and free-energy
expansion / closed-form / lower-bound / upper-bound / `lower_le_upper`
wrappers on `latticeGraph d`, plus
`correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A`, now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansion`.
Sandwich and downstream wrappers continue to live in this module
(sharper-exp wrappers were further moved to `HighTemperatureBoundsExpSharper`
in PR #1935; deviation / continuity wrappers were further moved to
`HighTemperatureBoundsDeviation` in PR #1936; ratio_sandwich / ratio_bound
wrappers were further moved to `HighTemperatureBoundsRatioBounds` in
PR #1937). The legacy import path is preserved by re-importing the new
child.
-/


/-- **ℤ^d Λ-level FV (3.46) numerator vanishes for odd-cardinality A**
at `h = 0`: `∑_{X : ∂X = A} tanh(β J)^|X| = 0` for any `A` of odd
cardinality. ℤ^d wrapper of `sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ`. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 :=
  sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ
    (IsingModel.latticeGraph d) Λ J β A hA_odd

/-- **ℤ^d Λ-level correlation nonnegativity from FV (3.46)** at `h = 0`:
under `0 ≤ β * J`, `0 ≤ correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ A`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_nonneg`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A :=
  correlationΛ_high_temp_h_zero_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ A

/-- **ℤ^d high-temperature even-subgraph sum is `≥ 1`**: under
`0 ≤ β * J`,
`∑_{X ⊆ E_Λ, even-degree} tanh(β J)^|X| ≥ 1` on the ℤ^d induced
subgraph. ℤ^d wrapper of `one_le_sum_pow_tanh_even_subgraph_Λ`. -/
theorem one_le_sum_pow_tanh_even_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑Λ) =>
            ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_Λ
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset is empty whenever `|A|` is odd.
ℤ^d wrapper of `high_temp_numerator_filter_eq_empty_of_odd_card_Λ`. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  high_temp_numerator_filter_eq_empty_of_odd_card_Λ
    (IsingModel.latticeGraph d) Λ A hA_odd

/-- **ℤ^d Z high-temp sandwich (FV (3.45))**: under `0 ≤ β·J`,
`2^|Λ| · cosh^|E_Λ| ≤ Z_Λ ≤ 2^(|Λ|+|E_Λ|) · cosh^|E_Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ (2 : ℝ) ^ (Λ.card +
            (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
          Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d freeEnergy high-temp sandwich (FV (3.45))**: under `0 < |Λ|`
and `0 ≤ β·J`,
`log 2 + (|E_Λ|/|Λ|) · log cosh(βJ) ≤ f_Λ ≤ log 2 + (|E_Λ|/|Λ|) · log(2·cosh βJ)`.
ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
    ∧ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_sandwich
    (IsingModel.latticeGraph d) Λ J β hβJ hne


/-! ## Moved: correlationΛ pair / singleton basic wrappers at h = 0

The §18.3-§18.4 concrete `correlationΛ_latticeGraph` basic high-temperature
wrappers at `h = 0` (pair nonneg, pair `≤ 1`, singleton / pair trivial-slice
vanishings at `J = 0` and `β = 0`, pair sandwich, singleton / pair
ferromagnetic, singleton `= 0 ∧ ≤ 1`, pair+singleton bundle) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationBasic`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **ℤ^d Λ pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩^Λ = 0`, `0 ≤ ⟨σ_iσ_j⟩^Λ`, and
`⟨σ_iσ_j⟩^Λ ≤ 1` into a single triple. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j

/-- **ℤ^d Λ pair + singleton complete-summary bundle at h = 0**: under
`0 ≤ β·J`, packages pair upper bound, pair sandwich lower, singleton
vanishing, and pair vanishing at `J = 0` / `β = 0` trivial slices. ℤ^d
wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 ∧
      0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both pair and singleton ℤ^d Λ-correlations
vanish. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 ∧
      correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (IsingModel.latticeGraph d) Λ J β i j

/-- **ℤ^d Λ pair correlation single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ β·J` and an edge `s(i, j) ∈ (inducedGraph (latticeGraph d) Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (IsingModel.latticeGraph d) Λ J β hβJ i j hij he


/-! ## Moved: §18.7 high-temperature exponential decay capstones

The §18.7 high-temperature pair-correlation exponential-decay capstone
wrappers on `latticeGraph d` at `h = 0` (16 theorems drawn from five
capstone families `tanh_pow_dist` / `exp_rate_dist` /
`exp_highTempExpRate_dist` / `exp_alpha_dist` /
`exp_alpha_dist_of_le_highTempExpRate`, in their
`correlationΛ_latticeGraph` / `correlationAlongExhaustion_latticeGraph`
versions and the ferromagnetic variants that previously lived alongside
them; some named-rate / monotone-rate ferromagnetic variants of
`exp_highTempExpRate_dist` continue to live in
`Concrete/LatticeGraphCorrelation/CorrelationDecay.lean` and are
intentionally not moved) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDecayCapstones`.
The legacy import path is preserved by re-importing the new child.
-/


/-- **ℤ^d Λ pair correlation strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge in `inducedGraph (latticeGraph d) Λ`,
`0 < ⟨σ_iσ_j⟩^Λ`. ℤ^d wrapper of
`correlationΛ_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    (IsingModel.latticeGraph d) Λ J β hβJ i j hij he

/-- **ℤ^d Λ ferromagnetic pair single-edge tanh lower bound (GJ §18.3 / FV (3.46))**:
under `0 ≤ J, 0 < β` and an edge in `inducedGraph (latticeGraph d) Λ`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. ℤ^d wrapper. -/
theorem
    correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j hij he

/-- **ℤ^d Λ ferromagnetic pair strict positivity under edge (GJ §18.3 / FV (3.46))**:
under `0 < J, 0 < β` and an edge in `inducedGraph (latticeGraph d) Λ`,
`0 < ⟨σ_iσ_j⟩^Λ`. ℤ^d wrapper. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ i j hij he

/-- **ℤ^d Λ pair single-edge tanh lower bound via lattice adjacency**:
under `0 ≤ β·J` and `(latticeGraph d).Adj ↑i ↑j` (i.e.
`latticeDistance d ↑i ↑j = 1`),
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. Direct corollary of
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`,
removing the explicit edge-set membership in favour of the more
familiar lattice adjacency on the ambient lattice. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ)
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) := by
  have hne : i ≠ j := by
    intro h
    apply hij.ne
    exact congrArg Subtype.val h
  have he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).mpr hij
  exact correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    d Λ J β hβJ i j hne he

/-- **ℤ^d Λ pair strict positivity via lattice adjacency**: under
`0 < β·J` and `(latticeGraph d).Adj ↑i ↑j`,
`0 < ⟨σ_iσ_j⟩^Λ`. Direct corollary of
`correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (i j : ↑Λ)
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    0 < correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) := by
  have hne : i ≠ j := by
    intro h
    apply hij.ne
    exact congrArg Subtype.val h
  have he : s(i, j) ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).mpr hij
  exact correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_edge
    d Λ J β hβJ i j hne he

/-- **ℤ^d Λ-level magnetization vanishes at h = 0**:
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i} = 0` for any `i : ↑Λ`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_at_singleton`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_singleton
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ-level Z₂ symmetry of correlation at h = 0 via handshake**:
for `A : Finset ↑Λ` of odd cardinality,
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ A = 0`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_odd_card_eq_zero`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_odd_card_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_high_temp_h_zero_odd_card_eq_zero
    (IsingModel.latticeGraph d) Λ J β A hA_odd

/-- **ℤ^d Λ Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
single statement bundling Λ Z bounds and trivial-slice values. ℤ^d
wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Λ.card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ (2 : ℝ) ^ (Λ.card +
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card) *
            Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card ∧
      partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ freeEnergy complete-summary bundle at h = 0**: under
`0 < |Λ|` and `0 ≤ β·J`, single statement bundling Λ-level lower /
upper bounds and trivial-slice values at `J = 0` / `β = 0` (both =
`log 2`). ℤ^d wrapper of
`freeEnergyΛ_high_temp_h_zero_complete_summary`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_complete_summary
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ Real.log 2 +
            ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
              Λ.card * Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ hne


/-! ## Moved: sharper-exp Z/f/log Z high-temperature bounds at h = 0

The §18.3-§18.4 concrete sharper-exp upper-bound / sandwich / complete-summary
wrappers on `latticeGraph d` at `h = 0` (17 theorems for
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_*_exp` families,
with ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpSharper`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: f/Z/log Z deviation / continuity wrappers at h = 0

The §18.3-§18.4 concrete deviation_bound / continuity_bundle /
deviation_sandwich / relative_sandwich / deviation_pos / pow_two_lt /
strict_deviation_bundle wrappers on `latticeGraph d` at `h = 0` (18 theorems
for `freeEnergyΛ_latticeGraph`, `partitionFunctionΛ_latticeGraph`, and
`log_partitionFunctionΛ_latticeGraph`, with ferromagnetic variants) now
live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsDeviation`.
The legacy import path is preserved by re-importing the new child.
-/



/-! ## Moved: Λ-level Z/f/log Z ratio sandwich and ratio bound wrappers

The §18.3-§18.4 concrete Λ-level `ratio_sandwich` / `ratio_bound` wrappers
on `latticeGraph d` at `h = 0` (29 theorems for
`partitionFunctionΛ_latticeGraph`, `freeEnergyΛ_latticeGraph`, and
`log_partitionFunctionΛ_latticeGraph` with `J = 0` / `β = 0` / `bundle` /
`triple_*` variants plus ferromagnetic counterparts) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsRatioBounds`.
The legacy import path is preserved by re-importing the new child.
-/



/-! ## Moved: alongExhaustion correlation/sandwich basic wrappers at h = 0

The §18.3-§18.4 concrete alongExhaustion basic wrappers on `latticeGraph d`
at `h = 0` (25 theorems for `correlationAlongExhaustion_latticeGraph`
closed form, nonneg, sandwich, ferromagnetic, trivial-slice vanishings,
pair_sandwich, pair_singleton_bundle, pair_pos_of_edge,
singleton, odd_card_eq_zero; plus `partitionFunctionAlongExhaustion_latticeGraph`
and `freeEnergyAlongExhaustion_latticeGraph` sandwich; plus the high-temp
numerator filter helper) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionBasic`.
The two `_of_latticeAdj` along-exhaustion variants stay below in this
module because they directly invoke the Λ-level `_of_latticeAdj` versions
(which also live here). The legacy import path is preserved by
re-importing the new child.
-/

/-- **ℤ^d along-ex pair single-edge tanh lower bound via lattice adjacency
at stage `n`**: under `0 ≤ β·J` and `(latticeGraph d).Adj ↑i ↑j` for
`i, j : ↑(Λ.volume n)`, the lifted pair correlation satisfies the
single-edge tanh lower bound. -/
theorem
correlationAlongExhaustion_latticeGraph_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n))
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    Real.tanh (β * J) /
        (2 : ℝ) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_of_latticeAdj
    d (Λ.volume n) J β hβJ i j hij

/-- **ℤ^d along-ex pair strict positivity via lattice adjacency at stage `n`**:
under `0 < β·J` and `(latticeGraph d).Adj ↑i ↑j`,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ) (i j : ↑(Λ.volume n))
    (hij : (IsingModel.latticeGraph d).Adj ↑i ↑j) :
    0 < correlationΛ (IsingModel.latticeGraph d) (Λ.volume n)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    d (Λ.volume n) J β hβJ i j hij


/-- **ℤ^d along-exhaustion general-h subset expansion (GJ §18.3)**:
at every stage `n`,
`Z_n(p) = (cosh βJ)^|E_n| · ∑_X tanh(βJ)^|X| · ∑_σ (∏_{e ∈ X} σ_iσ_j) exp(βh ∑ σ_i)`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_subset_form`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_subset_form
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n =
      Real.cosh (p.β * p.J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ↑(Λ.volume n),
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h *
                      ∑ i : ↑(Λ.volume n), Spin.sign ℝ (σ i)) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_subset_form
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d along-exhaustion high-temperature even-subgraph sum is `≥ 1`**:
under `0 ≤ β * J`,
`∑_{X ⊆ E_{Λ_n}, even-degree} tanh(β J)^|X| ≥ 1` at every stage `n`.
ℤ^d wrapper of `one_le_sum_pow_tanh_even_subgraph_alongExhaustion`. -/
theorem one_le_sum_pow_tanh_even_subgraph_alongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_alongExhaustion
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion FV (3.45) at `J = 0` consistency check**:
`Z_n(⟨0, 0, β⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_J_zero
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d along-exhaustion FV (3.45) at `β = 0` consistency check**:
`Z_n(⟨J, 0, 0⟩) = 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed_at_beta_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex Z complete-summary bundle at h = 0**: under `0 ≤ β·J`,
at every stage `n` packages along-exhaustion Z lower bound, upper bound,
and trivial-slice values at `J = 0` / `β = 0`. ℤ^d wrapper of
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary`. -/
theorem
    partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ (2 : ℝ) ^ ((Λ.volume n).card +
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) *
            Real.cosh (β * J) ^
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card ∧
      partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n = (2 : ℝ) ^ (Λ.volume n).card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex freeEnergy complete-summary bundle at h = 0**: under
`0 ≤ β·J` and `(Λ.volume n).Nonempty`, at every stage `n` packages
along-exhaustion freeEnergy lower / upper bounds and trivial-slice
values at `J = 0` / `β = 0` (both = `log 2`). ℤ^d wrapper of
`freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary`. -/
theorem
    freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.log 2 +
            ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
              (Λ.volume n).card *
                Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, 0, β⟩ : IsingParams ℝ) n = Real.log 2 ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, 0⟩ : IsingParams ℝ) n = Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ n hne


/-! ## Moved: alongExhaustion sharper-exp Z/f/log Z wrappers at h = 0

The §18.3-§18.4 concrete alongExhaustion sharper-exp upper-bound /
sandwich / complete-summary wrappers on `latticeGraph d` at `h = 0`
(17 theorems for
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`
with ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionExpSharper`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion f/Z/log Z deviation / continuity wrappers

The §18.3-§18.4 concrete alongExhaustion deviation_bound_exp /
continuity_bundle / deviation_sandwich / relative_sandwich /
deviation_pos / pow_two_lt / strict_deviation_bundle wrappers on
`latticeGraph d` at `h = 0` (18 theorems for
`freeEnergyAlongExhaustion_latticeGraph`,
`partitionFunctionAlongExhaustion_latticeGraph`, and
`log_partitionFunctionAlongExhaustion_latticeGraph` with ferromagnetic
variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionDeviation`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion Z/f/log Z ratio sandwich/ratio bound wrappers

The §18.3-§18.4 concrete alongExhaustion ratio_sandwich_bundle /
ratio_bound wrappers on `latticeGraph d` at `h = 0` now live in three
narrow children: the 8 residual `partitionFunctionAlongExhaustion_latticeGraph`
Z ratio wrappers remain in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioBounds`;
the 7 `triple_ratio_*` wrappers (sandwich + bound bundles, J = 0 /
β = 0 / ferromagnetic variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionTripleRatio`
(narrowed in PR #1996); and the 14 `log_partitionFunction` /
`freeEnergy` ratio wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionRatioLogFe`
(narrowed in PR #1997). The legacy import path is preserved by
re-importing all three children.
-/

/-- **ℤ^d along-exhaustion partition function high-temperature closed form (FV §3.7.3 eq. (3.45))**:
at every stage `n`,
`partitionFunctionAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  = 2^|Λ_n| · cosh(βJ)^|E_{Λ_n}| · ∑_{X ⊆ E_{Λ_n}, even-degree} tanh(βJ)^|X|`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑(Λ.volume n),
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-exhaustion correlation nonnegativity from FV (3.46)**:
under `0 ≤ β * J`,
`0 ≤ correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ A n`
at every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_nonneg`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_high_temp_h_zero_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ A n

/-- **ℤ^d along-exhaustion partition function high-temperature lower bound (FV (3.45))**:
under `0 ≤ β * J`, at every stage `n`,
`partitionFunctionAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  ≥ 2^|Λ_n| · (cosh(βJ))^|E_{Λ_n}|`.
ℤ^d wrapper of `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_lower_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-exhaustion free-energy high-temperature lower bound from FV (3.45)**:
under `0 ≤ β * J` and `0 < |Λ_n|`, at stage `n`,
`freeEnergyAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ n
  ≥ log 2 + (|E_{Λ_n}|/|Λ_n|) · log(cosh(β·J))`.
ℤ^d wrapper of `freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_lower_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n hne


/-! ## Moved: freeEnergyInfinite high-temperature wrappers

The §18.3-§18.4 concrete `freeEnergyInfinite` high-temperature wrappers
on `latticeGraph d` (with caller-supplied `Exhaustion` BED witness) and
on `cubicExhaustion d` (with the BED constant `c = d`) (10 theorems:
`upper_bound_exp_uniform`, `upper_bound_exp`, `sandwich_exp`,
`complete_summary_exp`, `deviation_bound_exp`,
`continuity_at_J_zero`, `continuity_at_beta_zero`, `continuity_bundle`,
`deviation_sandwich_exp`, `ratio_bound_bundle`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsFreeEnergyInfinite`.
The legacy import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
