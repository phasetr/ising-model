import IsingModel.AmbientLattice.Defs.HighTempPartition
import IsingModel.AmbientLattice.Defs.Correlation
import IsingModel.Conditioning.CorrelationRates

/-!
# Ambient lattice high-temperature correlations

High-temperature correlation and magnetization wrappers at the ambient
finite-volume layer.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level FV (3.46) numerator vanishes for odd-cardinality A** at `h = 0`:
for `A : Finset ↑Λ` of odd cardinality,
`∑_{X ⊆ E_Λ : ∂X = A} tanh(β J)^|X| = 0`.
Direct lift of `IsingModel.sum_high_temp_numerator_h_zero_odd_card_eq_zero`
(Step 291) through the induced subgraph on `Λ`. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 :=
  IsingModel.sum_high_temp_numerator_h_zero_odd_card_eq_zero
    (inducedGraph G Λ) J β A hA_odd

/-- **Λ-level correlation nonnegativity from FV (3.46)** at `h = 0`:
under `0 ≤ β * J`, `0 ≤ correlationΛ G Λ ⟨J, 0, β⟩ A`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_nonneg`
(Step 293) through `correlationΛ_apply`. -/
theorem correlationΛ_high_temp_h_zero_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_nonneg
    (inducedGraph G Λ) J β hβJ A

/-- **Λ-level §18.7 capstone: high-temperature exponential decay of
the pair correlation in graph distance**. Under `0 ≤ β·J`, for
`i, j : ↑Λ`,
`⟨σ_iσ_j⟩^{Λ}_{β,0} ≤ 2^{|E_Λ|} · tanh(β·J)^{(inducedGraph G Λ).dist i j}`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist`
(Step 574) through `correlationΛ_apply`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G Λ).dist i j := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (inducedGraph G Λ) J β hβJ i j

/-- **Λ-level §18.7 ferromagnetic capstone**: under `0 ≤ J, 0 < β`,
the same exponential-decay bound as the non-ferromagnetic Λ wrap. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.tanh (β * J) ^ (inducedGraph G Λ).dist i j :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    G Λ J β (mul_nonneg hβ.le hJ) i j

/-- **Λ-level rate-form §18.7 capstone**: under `0 ≤ β·J`, for
`i, j : ↑Λ`, the finite-volume pair-correlation distance bound is written
with the explicit decay rate `-log(tanh(β·J))`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G Λ).dist i j : ℝ)) := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    (inducedGraph G Λ) J β hβJ i j

/-- **Λ-level ferromagnetic rate-form §18.7 capstone**: under
`0 ≤ J, 0 < β`, the same explicit-rate pair-correlation bound holds on
the induced finite-volume graph. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-(-Real.log (Real.tanh (β * J))) *
          ((inducedGraph G Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_rate_dist
    G Λ J β (mul_nonneg hβ.le hJ) i j

/-- **Λ-level named-rate §18.7 capstone**: the induced finite-volume
pair-correlation distance bound written with `highTempExpRate`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) * ((inducedGraph G Λ).dist i j : ℝ)) := by
  rw [correlationΛ_apply]
  exact
    IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
      (inducedGraph G Λ) J β hβJ i j

/-- **Λ-level ferromagnetic named-rate §18.7 capstone**: under
`0 ≤ J, 0 < β`, the induced finite-volume pair-correlation distance
bound is written with `highTempExpRate`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-(highTempExpRate β J) * ((inducedGraph G Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_highTempExpRate_dist
    G Λ J β (mul_nonneg hβ.le hJ) i j

/-- **Λ-level monotone-rate §18.7 capstone**: any
`α ≤ -log(tanh(β·J))` may replace the exact high-temperature rate in the
finite-volume pair-correlation distance bound on the induced graph. -/
theorem correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G Λ).dist i j : ℝ)) := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    (inducedGraph G Λ) J β α hβJ hα i j

/-- **Λ-level named monotone-rate §18.7 capstone**: any
`α ≤ highTempExpRate β J` gives the induced-graph pair-correlation
distance bound with rate `α`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β α : ℝ) (hβJ : 0 ≤ β * J)
    (hα : α ≤ highTempExpRate β J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G Λ).dist i j : ℝ)) := by
  rw [correlationΛ_apply]
  simpa [highTempExpRate] using
    IsingModel.correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
      (inducedGraph G Λ) J β α hβJ hα i j

/-- **Λ-level ferromagnetic named monotone-rate §18.7 capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ highTempExpRate β J` gives the induced-graph
pair-correlation distance bound with rate `α`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_exp_alpha_dist_of_le_highTempExpRate_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ highTempExpRate β J) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_of_le_highTempExpRate
    G Λ J β α (mul_nonneg hβ.le hJ) hα i j

/-- **Λ-level ferromagnetic monotone-rate §18.7 capstone**: under
`0 ≤ J, 0 < β`, any `α ≤ -log(tanh(β·J))` gives the induced-graph
pair-correlation distance bound with rate `α`. -/
theorem
correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β α : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hα : α ≤ -Real.log (Real.tanh (β * J))) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card *
        Real.exp (-α * ((inducedGraph G Λ).dist i j : ℝ)) :=
  correlationΛ_high_temp_h_zero_at_pair_le_two_pow_edges_mul_exp_alpha_dist
    G Λ J β α (mul_nonneg hβ.le hJ) hα i j

/-- **Λ-level high-temperature even-subgraph sum is `≥ 1`**: under
`0 ≤ β * J`,
`∑_{X ⊆ E_Λ, even-degree at every v ∈ ↑Λ} tanh(β J)^|X| ≥ 1`.
Direct lift of `IsingModel.one_le_sum_pow_tanh_even_subgraph`
(Step 295) through the induced subgraph on `Λ`. -/
theorem one_le_sum_pow_tanh_even_subgraph_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (1 : ℝ) ≤ ∑ X ∈ (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) =>
          ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  IsingModel.one_le_sum_pow_tanh_even_subgraph (inducedGraph G Λ) J β hβJ

/-- **Λ-level FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset over which the FV (3.46) numerator sums is
*literally empty* whenever `|A|` is odd.
Direct lift of `IsingModel.high_temp_numerator_filter_eq_empty_of_odd_card`
(Step 297). -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    (inducedGraph G Λ).edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ↑Λ) => ∀ v : ↑Λ,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ :=
  IsingModel.high_temp_numerator_filter_eq_empty_of_odd_card
    (inducedGraph G Λ) A hA_odd

/-- **Λ-level Z₂ symmetry of correlation at h = 0 from FV (3.46) + handshake**:
for `A : Finset ↑Λ` of odd cardinality,
`correlationΛ G Λ ⟨J, 0, β⟩ A = 0`.
Direct lift of `IsingModel.correlation_high_temp_h_zero_odd_card_eq_zero`
(Step 298). -/
theorem correlationΛ_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (A : Finset ↑Λ) (hA_odd : Odd A.card) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_odd_card_eq_zero
    (inducedGraph G Λ) J β A hA_odd

/-- **Λ-level magnetization vanishes at h = 0**:
`correlationΛ G Λ ⟨J, 0, β⟩ {i} = 0` for any single site `i : ↑Λ`.
Specialization at `A = {i}`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G Λ J β {i} ?_
  rw [Finset.card_singleton]; exact ⟨0, rfl⟩

/-- **Λ-level pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, `0 ≤ correlationΛ G Λ ⟨J, 0, β⟩ {i, j}`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_nonneg G Λ J β hβJ {i, j}

/-- **Λ-level pair correlation ≤ 1**:
`correlationΛ G Λ ⟨J, 0, β⟩ {i, j} ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_le_one G Λ _ {i, j}

/-- **Λ-level singleton at β=0,h=0**: `correlationΛ G Λ ⟨J,0,0⟩ {i} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_singleton_beta_zero
    (inducedGraph G Λ) J i

/-- **Λ-level pair at β=0,h=0**: `correlationΛ G Λ ⟨J,0,0⟩ {i,j} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_beta_zero
    (inducedGraph G Λ) J i j

/-- **Λ-level singleton at J=0,h=0**: `correlationΛ G Λ ⟨0,0,β⟩ {i} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_singleton_J_zero
    (inducedGraph G Λ) β i

/-- **Λ-level pair at J=0,h=0**: `correlationΛ G Λ ⟨0,0,β⟩ {i,j} = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (i j : ↑Λ) :
    correlationΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) = 0 := by
  rw [correlationΛ_apply]
  exact IsingModel.correlation_high_temp_h_zero_at_pair_J_zero
    (inducedGraph G Λ) β i j

/-- **Λ-pair sandwich at h=0**: `0 ≤ correlationΛ G Λ ⟨J,0,β⟩ {i,j} ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  ⟨correlationΛ_high_temp_h_zero_at_pair_nonneg G Λ J β hβJ i j,
   correlationΛ_high_temp_h_zero_at_pair_le_one G Λ J β i j⟩

/-- **Λ-pair ferromagnetic at h=0**: `0 ≤ J, 0 < β` → pair sandwich. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) :
    0 ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_sandwich G Λ J β
    (mul_nonneg hβ.le hJ) i j

/-- **Λ singleton ferromagnetic vanish**: `0 ≤ J, 0 < β` → `⟨σ_i⟩^Λ = 0`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 :=
  correlationΛ_high_temp_h_zero_at_singleton G Λ J β i

/-- **Λ singleton sandwich at h = 0**: `⟨σ_i⟩^Λ = 0 ∧ ≤ 1`. -/
theorem correlationΛ_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) = 0 ∧
      correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset ↑Λ) ≤ 1 :=
  ⟨correlationΛ_high_temp_h_zero_at_singleton G Λ J β i,
   (correlationΛ_high_temp_h_zero_at_singleton G Λ J β i).symm ▸ zero_le_one⟩

/-- **Λ transport of the project-derived pair single-edge tanh lower bound.**
under `0 ≤ β·J` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|` where `i, j : ↑Λ`. Λ-layer wrapper
of `correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑Λ) := by
  rw [correlationΛ_apply]
  exact correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (inducedGraph G Λ) J β hβJ i j hij he

/-- **Λ transport of project-derived pair strict positivity under an edge.**
under `0 < β·J` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`0 < ⟨σ_iσ_j⟩^Λ`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_pos_of_edge`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    0 < correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑Λ) := by
  rw [correlationΛ_apply]
  exact correlation_high_temp_h_zero_at_pair_pos_of_edge
    (inducedGraph G Λ) J β hβJ i j hij he

/-- **Λ ferromagnetic specialization of the project-derived pair lower bound.**
under `0 ≤ J, 0 < β` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`⟨σ_iσ_j⟩^Λ ≥ tanh(β·J) / 2^|E_Λ|`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
          ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G Λ J β (mul_nonneg hβ.le hJ) i j hij he

/-- **Λ ferromagnetic specialization of project-derived pair strict positivity.**
under `0 < J, 0 < β` and an edge `s(i, j) ∈ (inducedGraph G Λ).edgeSet`,
`0 < ⟨σ_iσ_j⟩^Λ`. Λ-layer wrapper of
`correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic`. -/
theorem correlationΛ_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (i j : ↑Λ) (hij : i ≠ j)
    (he : s(i, j) ∈ (inducedGraph G Λ).edgeSet) :
    0 < correlationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_pos_of_edge
    G Λ J β (mul_pos hβ hJ) i j hij he

end Ambient

end IsingModel
