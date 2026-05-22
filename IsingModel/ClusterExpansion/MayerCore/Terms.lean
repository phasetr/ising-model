import IsingModel.ClusterExpansion.RegularityHZero

/-!
# Cluster Expansion Mayer Core Terms

Mechanical child split from `ClusterExpansion/MayerCore.lean`.
-/

namespace IsingModel

open Finset

/-- **VD polymer-family sum has explicit polynomial derivative** (Step 575):
the polymer-family sum `t ↦ ∑_{Γ} ∏_{P ∈ Γ} t^|P|` has derivative at every
`t : ℝ` given by the explicit polynomial formula obtained from the product
rule. Specifically the derivative equals
`∑_{Γ} ∑_{Q ∈ Γ} (∏_{P ∈ Γ.erase Q} t^|P|) · ((|Q| : ℝ) · t^(|Q|-1))`,
which is itself a polynomial in `t`. Strengthens
`vdPolymerFamilies_sum_differentiable` (Step 558) by providing the
explicit derivative; closes the §18.6 deferred item "HasDerivAt with
explicit polynomial derivative" tracked in #1344. The proof combines
`HasDerivAt.fun_finset_prod` (product rule), `hasDerivAt_pow` (monomial),
and `HasDerivAt.fun_sum` (linearity). -/
theorem vdPolymerFamilies_sum_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t := by
  refine HasDerivAt.fun_sum (fun Γ _ => ?_)
  have h := HasDerivAt.fun_finset_prod (u := Γ)
    (f := fun P : Finset (Sym2 ι) => fun s : ℝ => s ^ P.card)
    (f' := fun P : Finset (Sym2 ι) => (P.card : ℝ) * t ^ (P.card - 1))
    (x := t) (fun P _ => hasDerivAt_pow P.card t)
  simpa [smul_eq_mul] using h

/-- **Mayer expansion n-th term** (Step 587, Mayer expansion):
the contribution of `n`-element polymer sequences to `log Ξ`:
`mayerExpansionTerm G n t = ∑_{ω ∈ piFinset (allPolymers G)} ϕ^T(ω) · z(t, ω)`.
The factor `1/n!` is already absorbed into the Ursell coefficient
(Step 583), so the Mayer expansion is
`log Ξ = ∑_{n ≥ 1} mayerExpansionTerm G n t`. -/
noncomputable def mayerExpansionTerm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
    ursellCoefficient ω * clusterSeqActivity t ω

/-- **n=0 Mayer term vanishes**: `mayerExpansionTerm G 0 t = 0`.
The unique `ω : Fin 0 → polymers` is the empty function;
`connectedSpanningEdgeSubsets` of the empty graph on `Fin 0` is empty
(`Connected` requires `Nonempty`), so `ursellCoefficient empty = 0`. -/
theorem mayerExpansionTerm_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 0 t = 0 := by
  unfold mayerExpansionTerm
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  refine mul_eq_zero.mpr (Or.inl ?_)
  apply ursellCoefficient_eq_zero_of_disconnected
  intro h
  exact (h.nonempty.elim Fin.elim0)

/-- **n=1 Mayer term equals total polymer activity**:
`mayerExpansionTerm G 1 t = ∑_{P ∈ allPolymers G} t^|P|`.
For `n = 1`, every singleton sequence has `ϕ^T = 1` (Step 583, with
the `1/1!` factor absorbed) and `z(t, ω) = t^|ω 0|` (Step 581). The
sum over `Fin 1 → allPolymers G` reindexes to a sum over `allPolymers G`. -/
theorem mayerExpansionTerm_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 1 t =
      ∑ P ∈ allPolymers G, t ^ P.card := by
  unfold mayerExpansionTerm
  apply Finset.sum_bij (fun (ω : Fin 1 → Finset (Sym2 ι)) (_ : ω ∈ _) => ω 0)
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    exact hω 0
  · intro ω₁ _ ω₂ _ heq
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact heq
  · intro P hP
    refine ⟨fun _ => P, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro _
    exact hP
  · intro ω _
    rw [ursellCoefficient_singleton, clusterSeqActivity_singleton, one_mul]

/-- **Cluster-sequence activity is continuous in `t`** (Step 588):
the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|` is a
finite product of monomials, hence continuous in `t`. -/
theorem clusterSeqActivity_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    Continuous (fun t : ℝ => clusterSeqActivity t ω) := by
  unfold clusterSeqActivity
  refine continuous_finset_prod _ (fun i _ => ?_)
  exact continuous_id.pow _

/-- **Mayer expansion n-th term is continuous in `t`** (Step 588):
each term `mayerExpansionTerm G n t = ∑_ω ϕ^T(ω) · z(t, ω)` is a
finite sum of `(constant) · (continuous in t)`, hence continuous.
First step toward Mayer-expansion regularity matching `log Ξ`. -/
theorem mayerExpansionTerm_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ => mayerExpansionTerm G n t) := by
  unfold mayerExpansionTerm
  refine continuous_finset_sum _ (fun ω _ => ?_)
  exact continuous_const.mul (clusterSeqActivity_continuous ω)

/-- **Cluster-sequence activity is differentiable in `t`** (Step 589):
the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|` is a
finite product of monomials, hence differentiable in `t` on all of `ℝ`. -/
theorem clusterSeqActivity_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    Differentiable ℝ (fun t : ℝ => clusterSeqActivity t ω) := by
  unfold clusterSeqActivity
  refine Differentiable.fun_finset_prod (fun i _ => ?_)
  exact (differentiable_id (𝕜 := ℝ)).pow _

/-- **Mayer expansion n-th term is differentiable in `t`** (Step 589):
each term is a polynomial in `t` (constant Ursell coefficients times
monomial activity factors), hence differentiable. Strengthens
`mayerExpansionTerm_continuous` (Step 588) and prepares for analyticity. -/
theorem mayerExpansionTerm_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => mayerExpansionTerm G n t) := by
  unfold mayerExpansionTerm
  refine Differentiable.fun_sum (fun ω _ => ?_)
  exact (clusterSeqActivity_differentiable ω).const_mul _

/-- **Cluster-sequence activity is real-analytic at every `t`** (Step
590): the activity factor `clusterSeqActivity t ω = ∏ i, t ^ |ω i|`
is a finite product of monomials. By induction on the index Finset
`Finset.univ : Finset (Fin n)`, each monomial `s ↦ s^k` is analytic
(`AnalyticAt.pow` of `analyticAt_id`), and analyticity is preserved by
multiplication. -/
theorem clusterSeqActivity_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => clusterSeqActivity s ω) t := by
  classical
  unfold clusterSeqActivity
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) t)
  | insert i I hi ih =>
      have h_step : (fun s : ℝ => ∏ j ∈ insert i I, s ^ (ω j).card) =
          (fun s : ℝ => s ^ (ω i).card * ∏ j ∈ I, s ^ (ω j).card) := by
        funext s
        exact Finset.prod_insert hi
      rw [h_step]
      exact (analyticAt_id.pow _).mul ih

/-- **Mayer expansion n-th term is real-analytic at every `t`** (Step
590): each term is a polynomial in `t`, hence analytic. Strengthens
`mayerExpansionTerm_differentiable` (Step 589) via `AnalyticAt.fun_sum`
plus `AnalyticAt.const_mul`. -/
theorem mayerExpansionTerm_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => mayerExpansionTerm G n s) t := by
  unfold mayerExpansionTerm
  refine Finset.analyticAt_fun_sum _ (fun ω _ => ?_)
  exact analyticAt_const.mul (clusterSeqActivity_analyticAt ω t)

/-- **Mayer expansion n-th term `AnalyticOnNhd ℝ _ Set.univ`** (Step
590): the global form of `mayerExpansionTerm_analyticAt`. -/
theorem mayerExpansionTerm_analyticOnNhd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => mayerExpansionTerm G n s) Set.univ :=
  fun t _ => mayerExpansionTerm_analyticAt G n t

/-- **Mayer expansion partial sum** (Step 591): finite truncation of
the Mayer expansion through cluster size `N`,
`mayerPartialSum G N t = ∑_{n = 0..N} mayerExpansionTerm G n t`.
The full Mayer expansion `log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t`
is the limit of these partial sums; convergence follows from
Kotecky-Preiss-type bounds (deferred). -/
noncomputable def mayerPartialSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), mayerExpansionTerm G n t

/-- **Mayer partial sum is continuous in `t`** (Step 591). -/
theorem mayerPartialSum_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Continuous (fun t : ℝ => mayerPartialSum G N t) := by
  unfold mayerPartialSum
  refine continuous_finset_sum _ (fun n _ => ?_)
  exact mayerExpansionTerm_continuous G n

/-- **Mayer partial sum is differentiable in `t`** (Step 591). -/
theorem mayerPartialSum_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Differentiable ℝ (fun t : ℝ => mayerPartialSum G N t) := by
  unfold mayerPartialSum
  refine Differentiable.fun_sum (fun n _ => ?_)
  exact mayerExpansionTerm_differentiable G n

/-- **Mayer partial sum is real-analytic at every `t`** (Step 591). -/
theorem mayerPartialSum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => mayerPartialSum G N s) t := by
  unfold mayerPartialSum
  refine Finset.analyticAt_fun_sum _ (fun n _ => ?_)
  exact mayerExpansionTerm_analyticAt G n t

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ`** (Step 591). -/
theorem mayerPartialSum_analyticOnNhd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => mayerPartialSum G N s) Set.univ :=
  fun t _ => mayerPartialSum_analyticAt G N t

/-- **Mayer partial sum at `N = 0`**: only the `n = 0` term, which
vanishes (`mayerExpansionTerm_zero`). -/
theorem mayerPartialSum_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 0 t = 0 := by
  unfold mayerPartialSum
  rw [show ((0 : ℕ) + 1) = 1 from rfl, Finset.sum_range_one]
  exact mayerExpansionTerm_zero G t

/-- **Mayer partial sum at `N = 1`**: the leading non-trivial truncation
equals the total polymer activity. The `n = 0` term vanishes
(`mayerExpansionTerm_zero`) and the `n = 1` term equals
`∑_{P ∈ allPolymers G} t^|P|` (`mayerExpansionTerm_one`). -/
theorem mayerPartialSum_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 1 t = ∑ P ∈ allPolymers G, t ^ P.card := by
  unfold mayerPartialSum
  rw [show ((1 : ℕ) + 1) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
      mayerExpansionTerm_zero, mayerExpansionTerm_one, zero_add]

/-- **Mayer expansion `n = 2` term as explicit pair sum** (Step 593):
under `mayerExpansionTerm G 2 t = ∑_{(P, Q) ∈ allPolymers² with
PolymersIncompatible P Q} (-1/2) · t^|P| · t^|Q|`. The reindexing
`piFinset (Fin 2 → allPolymers G) ↔ allPolymers G ×ˢ allPolymers G`
sends `ω ↦ (ω 0, ω 1)`. The pair Ursell formula (Step 586) reduces
each summand to `(-1/2)` when incompatible and `0` otherwise. -/
theorem mayerExpansionTerm_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 2 t =
      ∑ pq ∈ (allPolymers G) ×ˢ (allPolymers G),
        (if PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ) else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) := by
  unfold mayerExpansionTerm
  -- Reindex piFinset (Fin 2, allPolymers) ↔ allPolymers ×ˢ allPolymers via ω ↔ (ω 0, ω 1).
  apply Finset.sum_bij
    (fun (ω : Fin 2 → Finset (Sym2 ι)) (_ : ω ∈ _) => (ω 0, ω 1))
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    rw [Finset.mem_product]
    exact ⟨hω 0, hω 1⟩
  · intro ω₁ _ ω₂ _ heq
    funext i
    fin_cases i
    · exact (Prod.mk.inj heq).1
    · exact (Prod.mk.inj heq).2
  · intro pq hpq
    rw [Finset.mem_product] at hpq
    refine ⟨fun i => if i = 0 then pq.1 else pq.2, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · simpa using hpq.1
      · simpa using hpq.2
    · rfl
  · intro ω hω
    rw [Fintype.mem_piFinset] at hω
    rw [ursellCoefficient_pair, clusterSeqActivity]
    simp only [Fin.prod_univ_two]

/-- **Mayer expansion term continuous in `β` (with `J` fixed)** (Step
594): chain composition of `mayerExpansionTerm_continuous` with
`continuous_real_tanh` and `Continuous.mul`. -/
theorem mayerExpansionTerm_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J : ℝ) :
    Continuous (fun β : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (mayerExpansionTerm_continuous G n).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer expansion term continuous in `J` (with `β` fixed)** (Step
594). -/
theorem mayerExpansionTerm_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β : ℝ) :
    Continuous (fun J : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (mayerExpansionTerm_continuous G n).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer partial sum continuous in `β` (with `J` fixed)** (Step
594). -/
theorem mayerPartialSum_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    Continuous (fun β : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (mayerPartialSum_continuous G N).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer partial sum continuous in `J` (with `β` fixed)** (Step
594). -/
theorem mayerPartialSum_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    Continuous (fun J : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (mayerPartialSum_continuous G N).comp (continuous_real_tanh.comp h_mul)

/-- **Mayer expansion term differentiable in `β` (with `J` fixed)**
(Step 595): chain rule with `differentiable_real_tanh` and the
linear factor `β ↦ β * J`. -/
theorem mayerExpansionTerm_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  exact (mayerExpansionTerm_differentiable G n).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).mul_const _))

/-- **Mayer expansion term differentiable in `J` (with `β` fixed)** (Step 595). -/
theorem mayerExpansionTerm_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => mayerExpansionTerm G n (Real.tanh (β * J))) := by
  exact (mayerExpansionTerm_differentiable G n).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).const_mul _))

/-- **Mayer partial sum differentiable in `β` (with `J` fixed)** (Step 595). -/
theorem mayerPartialSum_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  exact (mayerPartialSum_differentiable G N).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).mul_const _))

/-- **Mayer partial sum differentiable in `J` (with `β` fixed)** (Step 595). -/
theorem mayerPartialSum_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => mayerPartialSum G N (Real.tanh (β * J))) := by
  exact (mayerPartialSum_differentiable G N).comp
    (differentiable_real_tanh.comp ((differentiable_id (𝕜 := ℝ)).const_mul _))

/-- **Mayer expansion term real-analytic in `β` (with `J` fixed)**
(Step 596): chain of `mayerExpansionTerm_analyticAt` (Step 590),
`analyticAt_real_tanh`, and the analytic linear factor `β ↦ β·J`. -/
theorem mayerExpansionTerm_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => mayerExpansionTerm G n (Real.tanh (β' * J))) β := by
  have h_lin : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (mayerExpansionTerm_analyticAt G n _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer expansion term real-analytic in `J` (with `β` fixed)** (Step 596). -/
theorem mayerExpansionTerm_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => mayerExpansionTerm G n (Real.tanh (β * J'))) J := by
  have h_lin : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (mayerExpansionTerm_analyticAt G n _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum real-analytic in `β` (with `J` fixed)** (Step 596). -/
theorem mayerPartialSum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => mayerPartialSum G N (Real.tanh (β' * J))) β := by
  have h_lin : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (mayerPartialSum_analyticAt G N _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum real-analytic in `J` (with `β` fixed)** (Step 596). -/
theorem mayerPartialSum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => mayerPartialSum G N (Real.tanh (β * J'))) J := by
  have h_lin : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (mayerPartialSum_analyticAt G N _).comp ((analyticAt_real_tanh _).comp h_lin)

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ` in `β`** (Step 596). -/
theorem mayerPartialSum_tanh_analyticOnNhd_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => mayerPartialSum G N (Real.tanh (β' * J))) Set.univ :=
  fun β _ => mayerPartialSum_tanh_analyticAt_beta G N J β

/-- **Mayer partial sum `AnalyticOnNhd ℝ _ Set.univ` in `J`** (Step 596). -/
theorem mayerPartialSum_tanh_analyticOnNhd_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => mayerPartialSum G N (Real.tanh (β * J'))) Set.univ :=
  fun J _ => mayerPartialSum_tanh_analyticAt_J G N β J

end IsingModel
