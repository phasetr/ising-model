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

/-- **symmDiff of two overlapping pairs**: for `i ≠ j`, `i ≠ u`, `u ≠ j`,
`{i,j} △ {i,u} = {u,j}` as Finsets. -/
private lemma symmDiff_pair_pair_of_ne {α : Type*} [DecidableEq α] {i j u : α}
    (hij : i ≠ j) (hiu : i ≠ u) (huj : u ≠ j) :
    symmDiff ({i, j} : Finset α) {i, u} = {u, j} := by
  rw [symmDiff_def]
  have h1 : ({i, j} : Finset α) \ {i, u} = {j} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨h, hni, _⟩
      rcases h with rfl | rfl
      · exact absurd rfl hni
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, hij.symm, huj.symm⟩
  have h2 : ({i, u} : Finset α) \ {i, j} = {u} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨h, hni, _⟩
      rcases h with rfl | rfl
      · exact absurd rfl hni
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, hiu.symm, huj⟩
  rw [h1, h2]
  ext x; simp [or_comm]

set_option linter.unusedDecidableInType false in
/-- **Nonnegativity of correlation** via the weightSum ratio. -/
private lemma correlation_inducedGraph_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (A : Finset ↑Λ) :
    0 ≤ correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) A :=
  correlation_inducedGraph_eq_weightSum_ratio G Λ hβJ A ▸
    div_nonneg (Current.weightSum_nonneg G Λ A hβJ) (weightSum_empty_pos G Λ hβJ).le

set_option linter.unusedDecidableInType false in
/-- **High-temperature susceptibility bound** (Simon-Lieb iteration):
for `0 ≤ βJ`, `D` bounding the incident-edge count of every vertex, and `βJD < 1`,
`∑_{j≠i} ⟨σ_iσ_j⟩ ≤ βJD/(1-βJD)`.

**Proof**: iterate `correlation_inducedGraph_simon_lieb` via a fixed-point argument.
Define `T_k = ∑_{j≠k} ⟨σ_kσ_j⟩` and `M = max_k T_k`. Simon-Lieb + symmDiff computation
gives `T_k ≤ βJD(1+M)` for all `k`; taking `k = argmax T` yields
`M(1-βJD) ≤ βJD`, hence `M ≤ βJD/(1-βJD)`.

Reference: Glimm–Jaffe §5.1; Friedli–Velenik §3.7.3. -/
theorem correlation_sum_le_of_high_temp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    {D : ℕ} (hD : ∀ v : ↑Λ,
        (Finset.univ.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card ≤ D)
    (hlt : β * J * ↑D < 1) (i : ↑Λ) :
    ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ i),
      correlation (inducedGraph G Λ) (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ β * J * ↑D / (1 - β * J * ↑D) := by
  classical
  let G' := inducedGraph G Λ
  let p : IsingParams ℝ := ⟨J, 0, β⟩
  -- Susceptibility T_k = ∑_{j≠k} corr({k,j})
  let T : ↑Λ → ℝ := fun k =>
    ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ k), correlation G' p {k, j}
  suffices hTi : T i ≤ β * J * ↑D / (1 - β * J * ↑D) from hTi
  -- Nonnegativity
  have hcnn : ∀ k l : ↑Λ, 0 ≤ correlation G' p {k, l} :=
    fun k l => correlation_inducedGraph_nonneg G Λ hβJ {k, l}
  have hTnn : ∀ k : ↑Λ, 0 ≤ T k :=
    fun k => Finset.sum_nonneg fun j _ => hcnn k j
  -- ↑Λ nonempty since i : ↑Λ
  have hne : (Finset.univ : Finset ↑Λ).Nonempty := ⟨i, Finset.mem_univ i⟩
  -- Find the argmax k₀ of T
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ T hne
  -- Step 1: T k ≤ βJ·D·(1 + T k₀) for all k
  have hTle : ∀ k : ↑Λ, T k ≤ β * J * ↑D * (1 + T k₀) := by
    intro k
    let Ek := Finset.univ.filter (fun e : G'.edgeSet => k ∈ (e : Sym2 ↑Λ))
    -- Apply Simon-Lieb to each j ≠ k
    calc T k
        ≤ ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ k),
            β * J * ∑ e ∈ Ek,
              correlation G' p (symmDiff {k, j} (e : Sym2 ↑Λ).toFinset) :=
          Finset.sum_le_sum fun j hj =>
            correlation_inducedGraph_simon_lieb G Λ hβJ ((Finset.mem_filter.mp hj).2.symm)
      _ = β * J * ∑ e ∈ Ek,
            ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ k),
              correlation G' p (symmDiff {k, j} (e : Sym2 ↑Λ).toFinset) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ β * J * ∑ e ∈ Ek, (1 + T k₀) := by
          apply mul_le_mul_of_nonneg_left _ hβJ
          apply Finset.sum_le_sum
          intro e he
          -- Extract other endpoint u of edge e
          have hke : k ∈ (e : Sym2 ↑Λ) := (Finset.mem_filter.mp he).2
          set u := Sym2.Mem.other hke
          have hku : k ≠ u :=
            (Sym2.other_ne (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2) hke).symm
          have he_toFinset : (e : Sym2 ↑Λ).toFinset = {k, u} := by
            have h := @Sym2.toFinset_mk_eq _ _ k u
            rwa [Sym2.other_spec hke] at h
          rw [he_toFinset]
          -- Split sum at j = u using sum_erase_add
          let s := Finset.univ.filter (fun j : ↑Λ => j ≠ k)
          have hu_in : u ∈ s :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ u, hku.symm⟩
          calc ∑ j ∈ s, correlation G' p (symmDiff {k, j} {k, u})
              = ∑ j ∈ s.erase u, correlation G' p (symmDiff {k, j} {k, u}) +
                correlation G' p (symmDiff {k, u} {k, u}) :=
                  (Finset.sum_erase_add _ _ hu_in).symm
            _ = ∑ j ∈ s.erase u, correlation G' p (symmDiff {k, j} {k, u}) + 1 := by
                  simp only [symmDiff_self, Finset.bot_eq_empty, correlation_empty]
            _ = 1 + ∑ j ∈ s.erase u, correlation G' p (symmDiff {k, j} {k, u}) :=
                  add_comm _ _
            _ = 1 + ∑ j ∈ s.erase u, correlation G' p {u, j} := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hju : j ≠ u := Finset.ne_of_mem_erase hj
                  have hjk : j ≠ k :=
                    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
                  exact congrArg (correlation G' p)
                    (symmDiff_pair_pair_of_ne hjk.symm hku hju.symm)
            _ ≤ 1 + ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ u),
                  correlation G' p {u, j} := by
                  have hsub : ∑ j ∈ s.erase u, correlation G' p {u, j} ≤
                      ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ u),
                        correlation G' p {u, j} :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (fun j hj => Finset.mem_filter.mpr
                        ⟨Finset.mem_univ j, (Finset.mem_erase.mp hj).1⟩)
                      (fun j _ _ => hcnn u j)
                  linarith
            _ ≤ 1 + T k₀ := by
                  have hTu : ∑ j ∈ Finset.univ.filter (fun j : ↑Λ => j ≠ u),
                      correlation G' p {u, j} = T u := rfl
                  linarith [hk₀ u (Finset.mem_univ u)]
      _ = β * J * (↑Ek.card * (1 + T k₀)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ β * J * (↑D * (1 + T k₀)) := by
          apply mul_le_mul_of_nonneg_left _ hβJ
          apply mul_le_mul_of_nonneg_right _ (by linarith [hTnn k₀])
          exact_mod_cast hD k
      _ = β * J * ↑D * (1 + T k₀) := by ring
  -- Step 2: Fixed-point: T k₀ ≤ βJ·D·(1 + T k₀)
  have hMle : T k₀ ≤ β * J * ↑D * (1 + T k₀) := hTle k₀
  -- Step 3: T k₀ ≤ βJ·D/(1-βJ·D)
  have h1 : 0 < 1 - β * J * ↑D := by linarith
  have hMbound : T k₀ ≤ β * J * ↑D / (1 - β * J * ↑D) := by
    rw [le_div_iff₀ h1]; nlinarith
  -- Step 4: T i ≤ T k₀ ≤ bound
  linarith [hk₀ i (Finset.mem_univ i)]

end Ambient

end IsingModel
