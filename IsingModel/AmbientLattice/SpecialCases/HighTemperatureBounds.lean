import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds

/-!
# High-temperature expansion and bound wrappers along an exhaustion

Narrow child module for the §18.3-§18.4 high-temperature expansion,
lower/upper bound, sandwich, correlation, and deviation wrappers along an
exhaustion. The theorem names are the same as the former legacy declarations,
but callers can now avoid importing the monolithic special-cases legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-! ## Moved: alongExhaustion partition/free-energy expansion wrappers

The §18.3-§18.4 ambient alongExhaustion partition function / free energy
expansion / closed-form / lower-bound / upper-bound / sandwich /
complete-summary wrappers (20 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`,
`log_partitionFunctionAlongExhaustion`, `correlationAlongExhaustion` closed
forms, plus the `one_le_sum_pow_tanh_even_subgraph_alongExhaustion` helper)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion`.
The legacy import path is preserved by re-importing the new child.
-/


/-! ## Moved: alongExhaustion sharper-exp Z/f/log Z wrappers

The §18.3-§18.4 ambient alongExhaustion sharper-exp upper-bound /
sandwich / complete-summary wrappers (16 theorems for
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_*_exp`,
`freeEnergyAlongExhaustion_high_temp_h_zero_*_exp`, and
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_*_exp`
with ferromagnetic variants) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: alongExhaustion f/Z/log Z deviation / continuity wrappers

The §18.3-§18.4 ambient alongExhaustion deviation_bound_exp /
continuity_bundle / deviation_sandwich / relative_sandwich /
deviation_pos / pow_two_lt / strict_deviation_bundle wrappers (20
theorems for `freeEnergyAlongExhaustion`,
`partitionFunctionAlongExhaustion`, and
`log_partitionFunctionAlongExhaustion` with ferromagnetic variants)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: alongExhaustion Z/f/log Z ratio sandwich/ratio bound wrappers

The §18.3-§18.4 ambient alongExhaustion `ratio_sandwich` / `ratio_bound` /
`triple_ratio_*` / `_of_nonempty` wrappers (34 theorems for
`partitionFunctionAlongExhaustion`, `freeEnergyAlongExhaustion`, and
`log_partitionFunctionAlongExhaustion` with bundle / triple_* /
`_of_nonempty` variants plus ferromagnetic counterparts) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds`.
The legacy import path is preserved by re-importing the new child.
-/


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

/-- **Along-exhaustion correlation Z₂ symmetry at h = 0 (GJ §18.3)**:
for any ambient `A : Finset V` with odd cardinality, at every stage `n`
where `A ⊆ Λ.volume n`, the per-stage correlation
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0`.

When `A ⊄ Λ.volume n`, `correlationAlongExhaustion` is `0` by definition,
trivially satisfying the equation. When `A ⊆ Λ.volume n`, lift via
`liftFinset` (preserves cardinality) and apply
`correlationΛ_high_temp_h_zero_odd_card_eq_zero` (Step 299). -/
theorem correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · simp only [dif_pos hAn]
    have hcard : (liftFinset A hAn).card = A.card := liftFinset_card hAn
    refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G (Λ.volume n) J β
      (liftFinset A hAn) ?_
    rw [hcard]; exact hA_odd
  · simp only [dif_neg hAn]

/-- **Along-exhaustion FV (3.46) at A = ∅ consistency check**:
under `0 ≤ β·J`, at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ ∅ n = 1`.
The empty Finset is always a subset of `Λ.volume n`, so we lift via
`liftFinset`, then apply `correlationΛ_high_temp_h_zero_at_empty_A` (Step 314). -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_empty_A
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset V) n = 1 := by
  unfold correlationAlongExhaustion
  rw [dif_pos (Finset.empty_subset _)]
  have h_lift : liftFinset (∅ : Finset V) (Finset.empty_subset (Λ.volume n))
      = (∅ : Finset ↑(Λ.volume n)) := by
    ext v; simp [liftFinset]
  rw [h_lift]
  exact correlationΛ_high_temp_h_zero_at_empty_A G (Λ.volume n) J β hβJ

/-- **Along-ex pair correlation ≤ 1 at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_le_one G (Λ.volume n) _ _
  · rw [dif_neg hAn]; exact zero_le_one

/-- **Along-exhaustion pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n :=
  correlationAlongExhaustion_high_temp_h_zero_nonneg G Λ J β hβJ {i, j} n

/-- **Along-ex pair sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i, j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

/-- **Along-ex pair ferromagnetic sandwich at h = 0**: under `0 ≤ J, 0 < β`,
`0 ≤ correlationAlongExhaustion ⟨J,0,β⟩ {i,j} n ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) i j n

/-- **Along-ex pair at J=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨0, 0, β⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn, correlationΛ_J_zero, mul_zero, Real.tanh_zero]
    have hcard_pos : 0 < (liftFinset ({i, j} : Finset V) hAn).card := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact zero_pow hcard_pos.ne'
  · rw [dif_neg hAn]

/-- **Along-ex pair at β=0,h=0 vanishes**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, 0⟩ {i, j} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i, j} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    apply IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    have : (liftFinset ({i, j} : Finset V) hAn).card ≥ 1 := by
      rw [liftFinset_card]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    exact Finset.card_pos.mp this
  · rw [dif_neg hAn]

/-- **Along-ex singleton at J=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ 0 β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton at β=0,h=0 vanishes**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : ({i} : Finset V) ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_at_singleton_beta_zero
      G (Λ.volume n) J ⟨i, hAn (by simp)⟩
  · rw [dif_neg hAn]

/-- **Along-exhaustion magnetization vanishes at h = 0**: at every stage `n`,
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0` for any
ambient site `i : V`. Specialization at `A = {i}`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 := by
  refine correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    G Λ J β {i} ?_ n
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Along-ex singleton sandwich at h = 0**: `= 0 ∧ ≤ 1`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   (correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n).symm
      ▸ zero_le_one⟩

/-- **Along-ex pair+singleton bundle at h=0**. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n⟩

/-- **Along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_pair_le_one G Λ J β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

/-- **Along-ex pair + singleton trivial-slices full bundle at h = 0**:
at `J = 0` and `β = 0`, both pair and singleton correlations vanish at
every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 ∧
      correlationAlongExhaustion G Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset V) n = 0 :=
  ⟨correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero G Λ β i n,
   correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero G Λ J i n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero G Λ β i j n,
   correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero G Λ J i j n⟩

/-- **Along-ex pair+singleton bundle under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, packages `⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and
`⟨σ_iσ_j⟩ ≤ 1` at every stage `n`. Along-exhaustion wrapper of
`correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 ∧
      0 ≤ correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ∧
      correlationAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset V) n ≤ 1 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_bundle
    G Λ J β (mul_nonneg hβ.le hJ) i j n

/-- **Along-ex pair correlation single-edge tanh lower bound at stage `n` (GJ §18.3 / FV (3.46))**:
applies the Λ-level single-edge lower bound at the stage-`n`
subtype `↑(Λ.volume n)`. Along-exhaustion wrapper for
`correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G (Λ.volume n) J β hβJ i j hij he

/-- **Along-ex §18.7 capstone: high-temperature exponential decay of
the pair correlation in graph distance, at stage `n`**. Under
`0 ≤ β·J`, for `i, j : ↑(Λ.volume n)`,
`⟨σ_iσ_j⟩^{Λ_n}_{β,0} ≤ 2^{|E_{Λ_n}|} ·
    tanh(β·J)^{(inducedGraph G (Λ.volume n)).dist i j}`.
Stage-`n` Λ-level specialization of
`correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound at stage `n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G (Λ.volume n)).dist i j :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-- **Along-ex §18.7 rate-form capstone at stage `n`**: under
`0 ≤ β·J`, the pair-correlation distance bound at `Λ.volume n` is
written with the explicit decay rate `-log(tanh(β·J))`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex ferromagnetic §18.7 rate-form capstone at stage `n`**:
under `0 ≤ J, 0 < β`, the same explicit-rate pair-correlation bound
holds at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_rate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G Λ J β (mul_nonneg hβ.le hJ) n i j

/-- **Along-ex §18.7 named-rate capstone at stage `n`**: the stage-`n`
pair-correlation distance bound written with `highTempExpRate`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) *
          ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    G (Λ.volume n) J β hβJ i j

/-- **Along-ex §18.7 monotone-rate capstone at stage `n`**: any
`α ≤ -log(tanh(β·J))` may replace the exact high-temperature rate in the
pair-correlation distance bound at `Λ.volume n`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G (Λ.volume n) J β α hβJ hα i j

/-- **Along-ex §18.7 named monotone-rate capstone at stage `n`**:
any `α ≤ highTempExpRate β J` gives the stage-`n` pair-correlation
distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    G (Λ.volume n) J β α hβJ hα i j

/-- **Along-ex ferromagnetic §18.7 monotone-rate capstone at stage `n`**:
under `0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the stage-`n`
pair-correlation distance bound with rate `α`. -/
theorem
correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (n : ℕ)
    (i j : ↑(Λ.volume n)) :
    correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n))
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G (Λ.volume n)).dist i j : ℝ)) :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G Λ J β α (mul_nonneg hβ.le hJ) hα n i j

/-- **Along-ex pair correlation strict positivity under edge at stage `n` (GJ §18.3 / FV (3.46))**:
under `0 < β·J` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    G (Λ.volume n) J β hβJ i j hij he

/-- **Along-ex ferromagnetic pair single-edge tanh lower bound at stage `n`**:
under `0 ≤ J, 0 < β` and an edge in the stage-`n` induced subgraph,
`⟨σ_iσ_j⟩^{Λ_n} ≥ tanh(β·J) / 2^|E_{Λ_n}|`. Stage-`n` Λ-level
specialization of
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`. -/
theorem
    correlationAlongExhaustion_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    Real.tanh (β * J) /
        (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j hij he

/-- **Along-ex ferromagnetic pair strict positivity under edge at stage `n`**:
under `0 < J, 0 < β` and an edge in the stage-`n` induced subgraph,
`0 < ⟨σ_iσ_j⟩^{Λ_n}`. Stage-`n` Λ-level specialization of
`correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (n : ℕ)
    (i j : ↑(Λ.volume n)) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G (Λ.volume n)).edgeSet) :
    0 < correlationΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑(Λ.volume n)) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    G (Λ.volume n) J β hJ hβ i j hij he

/-- **Along-ex singleton ferromagnetic vanish at h = 0**: under
`0 ≤ J, 0 < β`, `correlationAlongExhaustion G Λ ⟨J, 0, β⟩ {i} n = 0`. -/
theorem correlationAlongExhaustion_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : V) (n : ℕ) :
    correlationAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset V) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton G Λ J β i n

end Ambient
end IsingModel
