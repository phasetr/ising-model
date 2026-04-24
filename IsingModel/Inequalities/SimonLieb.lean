import IsingModel.GibbsMeasure
import IsingModel.RandomCurrent

/-!
# Simon-Lieb inequality (GJ §5.1 / FV Prop. 9.31)

Connects the Gibbs-measure correlation function to the random-current
weight sums, then derives the Simon-Lieb inequality from
`Current.weightSum_pair_le_edge_sum` (PR #898).

Six supporting lemmas lead to the main result:
1. `edgeSpin_eq_spinEdgeProduct_of_inducedGraph_edgeSet` — bridge identity.
2. `boltzmannWeight_inducedGraph_eq_prod_exp_of_h_zero` — Boltzmann weight as edge product.
3. `pow_card_mul_weightSum_eq_sum_spinProduct_mul_boltzmannWeight` — RC ↔ Gibbs sum.
4. `partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty` — partition fn in RC terms.
5. `correlation_inducedGraph_eq_weightSum_ratio` — correlation as weightSum ratio.
6. `correlation_inducedGraph_simon_lieb` — the Simon-Lieb inequality.

References: Glimm–Jaffe §5.1 pp. 76–79; Friedli–Velenik Prop. 9.31 p. 428.
-/

namespace IsingModel

open Finset Real

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
omit [DecidableEq V] in
/-- **`edgeSpin` equals `spinEdgeProduct` on induced-graph edges**:
for any `σ : ↑Λ → Spin` and `e : (inducedGraph G Λ).edgeSet`,
`edgeSpin σ (↑e) = Config.spinEdgeProduct σ (↑e)`.
Both sides equal `(σ u).toSign * (σ v).toSign` for `e = {u, v}`. -/
theorem edgeSpin_eq_spinEdgeProduct_of_inducedGraph_edgeSet
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    edgeSpin (K := ℝ) σ (e : Sym2 ↑Λ) = Config.spinEdgeProduct σ (e : Sym2 ↑Λ) := by
  have hnd : ¬(e : Sym2 ↑Λ).IsDiag :=
    (inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.prop
  revert hnd
  refine (e : Sym2 ↑Λ).inductionOn (fun i j => ?_)
  intro hnd
  rw [Sym2.mk_isDiag_iff] at hnd
  unfold edgeSpin Config.spinEdgeProduct
  simp [Sym2.lift_mk, Sym2.toFinset_mk_eq,
        Finset.prod_insert (Finset.notMem_singleton.mpr hnd),
        Finset.prod_singleton, Spin.sign]

set_option linter.unusedDecidableInType false in
omit [DecidableEq V] in
/-- **Boltzmann weight at `h = 0` as an edge product**:
`boltzmannWeight (inducedGraph G Λ) ⟨J, 0, β⟩ σ = ∏_e exp(β J · spinEdgeProduct σ e)`.
Proof: unfold at `h = 0`, apply `Real.exp_sum` and `Finset.prod_subtype`,
then replace `edgeSpin` by `spinEdgeProduct`. -/
theorem boltzmannWeight_inducedGraph_eq_prod_exp_of_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {J β : ℝ} (σ : ↑Λ → Spin) :
    boltzmannWeight (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) σ
      = ∏ e : (inducedGraph G Λ).edgeSet,
          Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only [neg_zero, zero_mul, add_zero]
  rw [show -β * (-J * ∑ e ∈ (inducedGraph G Λ).edgeFinset, edgeSpin (K := ℝ) σ e) =
      β * J * ∑ e ∈ (inducedGraph G Λ).edgeFinset, edgeSpin (K := ℝ) σ e from by ring,
    Finset.mul_sum, Real.exp_sum]
  rw [Finset.prod_subtype (p := fun e => e ∈ (inducedGraph G Λ).edgeSet)
        (inducedGraph G Λ).edgeFinset
        (fun e => (inducedGraph G Λ).mem_edgeFinset)
        (fun e => Real.exp (β * J * edgeSpin (K := ℝ) σ e))]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [edgeSpin_eq_spinEdgeProduct_of_inducedGraph_edgeSet G Λ σ e]

set_option linter.unusedDecidableInType false in
/-- **Random-current identity `2^|Λ| · weightSum A = ∑_σ σ^A · boltzmannWeight σ`**:
for `0 ≤ β J` and `h = 0`. Combines `weightSum_eq_iSup` with
`CurrentBounded.pow_card_mul_iSup_weightSum_eq_sum_spinA_prod_exp`
and `boltzmannWeight_inducedGraph_eq_prod_exp_of_h_zero`. -/
theorem pow_card_mul_weightSum_eq_sum_spinProduct_mul_boltzmannWeight
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    (2 : ℝ) ^ Fintype.card ↑Λ * Current.weightSum G Λ A β J
      = ∑ σ : ↑Λ → Spin,
          spinProduct A σ * boltzmannWeight (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) σ := by
  rw [Current.weightSum_eq_iSup G Λ A hβJ,
      CurrentBounded.pow_card_mul_iSup_weightSum_eq_sum_spinA_prod_exp G Λ A hβJ]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [boltzmannWeight_inducedGraph_eq_prod_exp_of_h_zero G Λ σ]
  rfl

set_option linter.unusedDecidableInType false in
/-- **Partition function as `2^|Λ| · weightSum ∅`**: for `0 ≤ β J` and `h = 0`.
Uses the `A = ∅` case of `pow_card_mul_weightSum_eq_sum_spinProduct_mul_boltzmannWeight`
since `spinProduct ∅ σ = 1`. -/
theorem partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    partitionFunction (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ↑Λ * Current.weightSum G Λ ∅ β J := by
  unfold partitionFunction
  symm
  rw [pow_card_mul_weightSum_eq_sum_spinProduct_mul_boltzmannWeight G Λ hβJ ∅]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp [spinProduct]

set_option linter.unusedDecidableInType false in
/-- **`Current.weightSum G Λ ∅ β J` is positive** for `0 ≤ β J`:
derived from positivity of the partition function via
`partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty`. -/
private theorem weightSum_empty_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < Current.weightSum G Λ ∅ β J := by
  have hZ := partitionFunction_pos (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
  rw [partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty G Λ hβJ] at hZ
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ↑Λ := by positivity
  exact (mul_pos_iff.mp hZ).elim (·.2) (fun h => absurd h2 (not_lt.mpr h.1.le))

set_option linter.unusedDecidableInType false in
/-- **Correlation as weighted-sum ratio**: for `0 ≤ β J` and `h = 0`,
`correlation (inducedGraph G Λ) ⟨J,0,β⟩ A = weightSum A / weightSum ∅`.
Proof: numerator `2^|Λ| · weightSum A`, denominator `2^|Λ| · weightSum ∅`;
cancel `2^|Λ| > 0` via `field_simp`. -/
theorem correlation_inducedGraph_eq_weightSum_ratio
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) A
      = Current.weightSum G Λ A β J / Current.weightSum G Λ ∅ β J := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ↑Λ := by positivity
  have hW : 0 < Current.weightSum G Λ ∅ β J := weightSum_empty_pos G Λ hβJ
  unfold correlation gibbsExpectation
  rw [partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty G Λ hβJ,
      ← pow_card_mul_weightSum_eq_sum_spinProduct_mul_boltzmannWeight G Λ hβJ A]
  field_simp [h2.ne', hW.ne']

set_option linter.unusedDecidableInType false in
/-- **Simon-Lieb two-point edge-peeling inequality** (GJ §5.1 / FV Prop. 9.31, p. 428):
for `h = 0`, `0 ≤ β J`, and `i ≠ j ∈ Λ`,
`⟨σ_iσ_j⟩ ≤ βJ · ∑_{e ∋ i} ⟨σ^{{i,j}△endpoints(e)}⟩`.
This is the two-point, one-step peeling form of the Simon-Lieb inequality.
Proof: both sides equal `weightSum / weightSum ∅`; after cancelling the
positive denominator via `div_le_div_iff_of_pos_right`, reduces to
`weightSum_pair_le_edge_sum` (PR #898). -/
theorem correlation_inducedGraph_simon_lieb
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {i j : ↑Λ} (hij : i ≠ j) :
    correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J *
          ∑ e ∈ Finset.univ.filter (fun e : (inducedGraph G Λ).edgeSet => i ∈ (e : Sym2 ↑Λ)),
            correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
              (symmDiff {i, j} (e : Sym2 ↑Λ).toFinset) := by
  simp_rw [correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ]
  have hW : 0 < Current.weightSum G Λ ∅ β J := weightSum_empty_pos G Λ hβJ
  simp_rw [← Finset.sum_div, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hW).mpr (Current.weightSum_pair_le_edge_sum G Λ hij hβJ)

end Ambient

end IsingModel
