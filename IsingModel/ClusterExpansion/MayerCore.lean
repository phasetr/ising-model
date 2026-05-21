import IsingModel.ClusterExpansion.RegularityHZero

/-!
# Cluster expansion Mayer core and log bounds

Mechanical child split from `ClusterExpansion.lean`.
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

/-- **Mayer expansion `n = 2` term as filter sum** (Step 597): the
ordered-pair sum from Step 593 reduces to a sum over the incompatible
pairs only,
`mayerExpansionTerm G 2 t = (-1/2) · ∑_{(P, Q) ∈ allPolymers² with
PolymersIncompatible P Q} t^|P| · t^|Q|`.
The if-then-else summand vanishes on compatible pairs, so the sum
restricts to the filter `(allPolymers G ×ˢ allPolymers G).filter
(fun pq => PolymersIncompatible pq.1 pq.2)`. -/
theorem mayerExpansionTerm_two_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerExpansionTerm G 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
            (fun pq => PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) := by
  rw [mayerExpansionTerm_two]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]

/-- **Mayer expansion term vanishes at `t = 0`** (Step 598):
`mayerExpansionTerm G n 0 = 0` for every `n : ℕ`. For `n = 0`,
`ursellCoefficient` already vanishes (Step 587). For `n ≥ 1`, every
polymer `ω i` has `|ω i| ≥ 1`, so `0 ^ |ω i| = 0` and the product
`clusterSeqActivity 0 ω = ∏ i, 0 ^ |ω i|` contains a zero factor. -/
theorem mayerExpansionTerm_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) :
    mayerExpansionTerm G n 0 = 0 := by
  match n with
  | 0 => exact mayerExpansionTerm_zero G 0
  | k + 1 =>
    unfold mayerExpansionTerm
    refine Finset.sum_eq_zero (fun ω hω => ?_)
    rw [Fintype.mem_piFinset] at hω
    have h_polymer : IsPolymer G (ω 0) := mem_allPolymers.mp (hω 0)
    have h_pos : 0 < (ω 0).card := h_polymer.nonempty.card_pos
    have h_zero : (0 : ℝ) ^ (ω 0).card = 0 := zero_pow h_pos.ne'
    have h_prod : clusterSeqActivity (0 : ℝ) ω = 0 := by
      unfold clusterSeqActivity
      exact Finset.prod_eq_zero (Finset.mem_univ 0) h_zero
    rw [h_prod, mul_zero]

/-- **Mayer partial sum vanishes at `t = 0`** (Step 598): consequence
of `mayerExpansionTerm_at_zero` summed over `Finset.range (N + 1)`. -/
theorem mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    mayerPartialSum G N 0 = 0 := by
  unfold mayerPartialSum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  exact mayerExpansionTerm_at_zero G n

/-- **Polymer-family sum at `t = 0`** (Step 599):
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} 0^|P| = 1`. Only the
empty family `Γ = ∅` contributes (its empty product equals `1`); any
non-empty `Γ` contains a polymer with `|P| ≥ 1`, so `0^|P| = 0` and
the product vanishes. -/
theorem vdPolymerFamilies_sum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonempty_zero : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      Γ ≠ ∅ → (∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 := by
    intro Γ hΓ hne
    rw [mem_vdCompatiblePolymerFamilies] at hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hP_polymer : IsPolymer G P := mem_allPolymers.mp (hΓ.1 hP)
    have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
    exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.prod_empty]
  · intro Γ hΓ hne
    exact h_nonempty_zero Γ hΓ hne
  · intro h
    exact absurd h_empty_in h

/-- **`connectedSpanningEdgeSubsets` cardinality bound** (Step 602):
the connected-spanning edge subsets are a filter of the powerset of
`G.edgeFinset`, hence their count is at most `2^|G.edgeFinset|`. -/
theorem connectedSpanningEdgeSubsets_card_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (connectedSpanningEdgeSubsets G).card ≤ 2 ^ G.edgeFinset.card := by
  classical
  unfold connectedSpanningEdgeSubsets
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_powerset]

/-- **Ursell coefficient absolute bound** (Step 601): the triangle
inequality on the alternating-sign sum gives
`|ϕ^T(ω)| ≤ |connectedSpanningEdgeSubsets G(ω)| / n!`. Since each
summand `(-1)^|S|` has absolute value `1`, summing `|·|` gives the
cardinality of the index set. Useful for convergence estimates of the
Mayer expansion. -/
theorem ursellCoefficient_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      ((connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω)).card : ℝ)
        / n.factorial := by
  unfold ursellCoefficient
  rw [abs_div]
  have h_fact_abs : |((n.factorial : ℝ))| = n.factorial :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [h_fact_abs]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_each : ∀ S ∈ connectedSpanningEdgeSubsets (polymerSeqIncompatibilityGraph ω),
      |((-1 : ℝ) ^ S.card)| = 1 := by
    intro S _
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **Uniform Ursell coefficient bound** (Step 603): combining Step
601 (|ϕ^T| ≤ card / n!) and Step 602 (card ≤ 2^|E|) gives
`|ϕ^T(ω)| ≤ 2^|E(G(ω))| / n!`. The classical Mayer-expansion uniform
bound from connected-spanning subgraphs of the incompatibility graph. -/
theorem ursellCoefficient_abs_le_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤
      (2 ^ (polymerSeqIncompatibilityGraph ω).edgeFinset.card : ℝ)
        / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast connectedSpanningEdgeSubsets_card_le_pow _

/-- **Polymer-family sum ≥ 1 under `t ≥ 0`** (Step 605): for any
non-negative activity parameter `t`, the empty family `Γ = ∅`
contributes `1` and all other families contribute non-negative
products `∏ P ∈ Γ, t^|P| ≥ 0`. Hence the total is at least `1`.
This generalises `one_le_vdPolymerFamilies_sum` (Step 549) from the
tanh form to a generic non-negative activity. -/
theorem vdPolymerFamilies_sum_ge_one_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonneg : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      0 ≤ ∏ P ∈ Γ, t ^ P.card :=
    fun _ _ => Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)
  have h_empty_eq : (1 : ℝ) =
      ∏ P ∈ (∅ : Finset (Finset (Sym2 ι))), t ^ P.card := (Finset.prod_empty).symm
  rw [h_empty_eq]
  exact Finset.single_le_sum h_nonneg h_empty_in

/-- **Polymer-family sum ≤ `(1+t)^|E|` under `t ≥ 0`** (Step 629):
generic upper bound generalising Step 552's tanh-form bound. Proof:
`evenSubgraphs G ⊆ G.edgeFinset.powerset`, so the sum over even
subgraphs of `t^|X|` is at most the sum over all subsets, which equals
`(1+t)^|E|` by binomial expansion (`Finset.prod_one_add`). -/
theorem vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card := by
  classical
  rw [← evenSubgraphs_sum_eq_vdPolymerFamilies_sum G t,
      evenSubgraphs_eq_inline_filter]
  have hpower :
      (1 + t) ^ G.edgeFinset.card =
        ∑ X ∈ G.edgeFinset.powerset, t ^ X.card := by
    rw [← Finset.prod_const, Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.prod_const]
  rw [hpower]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro X _ _
  exact pow_nonneg ht _

/-- **Polymer-family sum > 0 under `t ≥ 0`** (Step 605):
strict positivity follows from `≥ 1` and `0 < 1`. Useful to ensure
`Real.log (vdPolymerFamilies_sum G t)` is well-defined. -/
theorem vdPolymerFamilies_sum_pos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card :=
  lt_of_lt_of_le zero_lt_one (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` is real-analytic at any `t ≥ 0`**
(Step 606): `AnalyticAt ℝ (Real.log ∘ vdPolymerFamilies_sum G) t` via
`AnalyticAt.log` (Step 561) plus positivity (Step 605). Sets up the
LHS of the Mayer expansion identity as a real-analytic function on
the non-negative axis. -/
theorem log_vdPolymerFamilies_sum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) t :=
  (vdPolymerFamilies_sum_analyticAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht)

/-- **`log (vdPolymerFamilies_sum)` AnalyticOnNhd over `[0, ∞)`**
(Step 607): global form of Step 606 — at every `t ∈ Set.Ici 0`, the
function is `AnalyticAt`, hence `AnalyticOnNhd ℝ _ (Set.Ici 0)`. -/
theorem log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ
      (fun s : ℝ => Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
                                 ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  fun _ ht => log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`Real.tanh` is non-negative under non-negative argument** (helper
for Step 608): `0 ≤ x → 0 ≤ Real.tanh x`. Uses `Real.sinh_nonneg_iff`
and `Real.cosh_pos`. -/
theorem real_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `β`**
(Step 608): under `0 ≤ β·J`, the function
`β' ↦ Real.log (∑_Γ ∏_{P ∈ Γ} tanh(β'·J)^|P|)` is `AnalyticAt ℝ` at `β`.
Combines Step 562 (vdSum analytic in β via tanh chain) with positivity
of vdSum at `tanh(β·J) ≥ 0` (Steps 605 + helper). -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_beta G J β).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`log (vdPolymerFamilies_sum tanh(β·J))` analyticAt in `J`**
(Step 608): dual of `_beta`. -/
theorem log_vdPolymerFamilies_sum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => Real.log
        (∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J := by
  refine (vdPolymerFamilies_sum_tanh_analyticAt_J G β J).log ?_
  exact vdPolymerFamilies_sum_pos_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Mayer expansion term absolute bound** (Step 604): the triangle
inequality applied to the Mayer term gives
`|mayerExpansionTerm G n t| ≤ ∑_ω |ϕ^T(ω)| · |z(t, ω)|`. -/
theorem mayerExpansionTerm_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    |mayerExpansionTerm G n t| ≤
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
        |ursellCoefficient ω| * |clusterSeqActivity t ω| := by
  unfold mayerExpansionTerm
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun ω _ => abs_mul _ _)

/-- **Uniform Ursell bound** (Step 615): independent-of-ω bound
`|ϕ^T(ω)| ≤ 2^(n choose 2) / n!`. Combines Step 603 (`2^|E(G(ω))| / n!`)
with Mathlib's `SimpleGraph.card_edgeFinset_le_card_choose_two`
(graph on `Fin n` has at most `n.choose 2` edges). -/
theorem ursellCoefficient_abs_le_choose_pow_div_factorial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ω : Fin n → Finset (Sym2 ι)) :
    |ursellCoefficient ω| ≤ (2 ^ (n.choose 2) : ℝ) / (n.factorial : ℝ) := by
  refine (ursellCoefficient_abs_le_pow_div_factorial ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two
              (G := polymerSeqIncompatibilityGraph ω)
  rw [show Fintype.card (Fin n) = n from Fintype.card_fin n] at h
  exact h

/-- **Mayer identity at `t = 0`** (Step 600, milestone): the first
verified instance of the Mayer expansion identity
`log Ξ = ∑_{n ≥ 0} mayerExpansionTerm G n t`. At `t = 0`,
both sides equal `0`:
- `log (vdPolymerFamilies_sum G 0) = log 1 = 0` via Step 599
- `mayerPartialSum G N 0 = 0` via Step 598

This is a trivial special case symbolically marking the structural
target. The general identity for non-zero `t` requires substantial
combinatorial work (Mayer/Ursell algebraic manipulations of formal
power series); it remains deferred. -/
theorem mayer_identity_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      mayerPartialSum G N 0 := by
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one, mayerPartialSum_at_zero]

/-- **Mayer identity at `β·J = 0`** (Step 609): trivial extension of
Step 600 to the β/J directions. When `β·J = 0`, `tanh(β·J) = 0`,
reducing both sides to the t=0 case. -/
theorem mayer_identity_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  rw [hβJ, Real.tanh_zero]
  exact mayer_identity_at_zero G N

/-- **Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G,
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_at_betaJ_zero G (mul_zero β) N


/-- **Polymer free energy** (Step 610): named wrapper for the LHS of
the Mayer expansion identity,
`polymerFreeEnergy G t := Real.log (∑_Γ ∏_{P ∈ Γ} t^|P|)`. The Mayer
identity then reads `polymerFreeEnergy G t = ∑_{n ≥ 0} mayerExpansionTerm G n t`
(general-`t` identity deferred). -/
noncomputable def polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) : ℝ :=
  Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)

/-- **`polymerFreeEnergy` at `t = 0`** (Step 610): equals `0` since
`vdPolymerFamilies_sum G 0 = 1`. -/
theorem polymerFreeEnergy_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 0 = 0 := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one]

/-- **`polymerFreeEnergy` analyticAt for `t ≥ 0`** (Step 610): direct
restatement of Step 606 in the named-wrapper form. -/
theorem polymerFreeEnergy_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`polymerFreeEnergy` AnalyticOnNhd over `[0, ∞)`** (Step 610). -/
theorem polymerFreeEnergy_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero G

/-- **`polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`** (Step 611):
direct consequence of analyticAt. -/
theorem polymerFreeEnergy_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).continuousAt

/-- **`polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`** (Step 611). -/
theorem polymerFreeEnergy_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).differentiableAt

/-- **Mayer identity at `t = 0` in `polymerFreeEnergy` form** (Step 611):
restatement of Step 600 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    polymerFreeEnergy G 0 = mayerPartialSum G N 0 := by
  rw [polymerFreeEnergy_at_zero, mayerPartialSum_at_zero]

/-- **freeEnergy decomposition with `polymerFreeEnergy`** (Step 612):
under `0 < |ι|` and `0 ≤ β·J`,
  `f = log 2 + (|E|/|ι|) · log cosh(β·J) + polymerFreeEnergy G (tanh(β·J)) / |ι|`.
Restatement of `freeEnergy_high_temp_expansion_h_zero_closed` (Step 317)
using the polymer-family form (Step 547 bijection wraps the
`evenSubgraphs` sum into the `vdCompatiblePolymerFamilies` form). -/
theorem freeEnergy_eq_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι := by
  rw [freeEnergy_high_temp_expansion_h_zero_closed G J β hβJ hne]
  unfold polymerFreeEnergy
  rw [← evenSubgraphs_eq_inline_filter,
      evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]

/-- **Ferromagnetic `freeEnergy = log 2 + ... + polymerFreeEnergy/|ι|`**
(Step 616): under `0 ≤ J`, `0 < β`, `0 < |ι|`, the Step 612 decomposition
holds (since `0 ≤ β·J` follows from `mul_nonneg`). -/
theorem freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι :=
  freeEnergy_eq_polymerFreeEnergy G J β (mul_nonneg hβ.le hJ) hne

/-- **Mayer identity at `β·J = 0` in `polymerFreeEnergy` form** (Step 617):
restate Step 609 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  unfold polymerFreeEnergy
  exact mayer_identity_at_betaJ_zero G hβJ N

/-- **Mayer identity at `β = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * J)) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (mul_zero β) N

/-- **`polymerFreeEnergy` analyticAt in `β`** (Step 613): named-wrapper
restatement of Step 608. -/
theorem polymerFreeEnergy_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) β :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_beta G J β hβJ

/-- **`polymerFreeEnergy` analyticAt in `J`** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) J :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_J G β J hβJ

/-- **`polymerFreeEnergy` AnalyticOnNhd in `β` over `[0, ∞)` (under
`0 ≤ J`)** (Step 613): for fixed `J ≥ 0`, the function is analytic at
every `β ≥ 0` since `0 ≤ β·J = β·J` follows from `mul_nonneg`. -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_beta_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) (Set.Ici 0) :=
  fun β hβ => polymerFreeEnergy_tanh_analyticAt_beta G J β (mul_nonneg hβ hJ)

/-- **`polymerFreeEnergy` AnalyticOnNhd in `J` over `[0, ∞)` (under
`0 ≤ β`)** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_J_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) (Set.Ici 0) :=
  fun J hJ => polymerFreeEnergy_tanh_analyticAt_J G β J (mul_nonneg hβ hJ)

/-- **`mayerPartialSum G 2 t` explicit formula** (Step 614):
`mayerPartialSum G 2 t = ∑_{P ∈ allPolymers G} t^|P|
                       - (1/2) ∑_{(P, Q) ∈ allPolymers², PolymersIncompatible P Q}
                          t^|P| · t^|Q|`.
The `N = 2` truncation of the Mayer expansion expressed entirely via
explicit polymer sums. Combines Step 592 (n=1: total polymer activity)
with Step 597 (n=2 filter form). -/
theorem mayerPartialSum_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 2 t =
      (∑ P ∈ allPolymers G, t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
              (fun pq => PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) := by
  unfold mayerPartialSum
  rw [show ((2 : ℕ) + 1) = 3 from rfl,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      mayerExpansionTerm_zero, mayerExpansionTerm_one,
      mayerExpansionTerm_two_filter, zero_add]

/-- **Mayer identity for empty-polymer graphs** (Step 618): when
`allPolymers G = ∅`, `polymerFreeEnergy G t = mayerPartialSum G N t = 0`
for any `t` and `N`. The polymer-family sum reduces to the empty
family contributing 1, so `log 1 = 0`; on the Mayer side, for `n ≥ 1`
every entry `ω i` would have to be in `allPolymers G = ∅`, an empty
domain, so the piFinset is empty and the sum vanishes. -/
theorem mayer_identity_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t := by
  classical
  have h_vd : vdCompatiblePolymerFamilies G = {∅} := by
    apply Finset.ext
    intro Γ
    rw [mem_vdCompatiblePolymerFamilies, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨h_sub, _⟩
      rw [h_no, Finset.subset_empty] at h_sub
      exact h_sub
    · intro h_eq
      refine ⟨?_, ?_⟩
      · rw [h_eq, h_no]
      · rw [h_eq]
        exact IsCompatiblePolymerFamilyVertexDisjoint.empty G
  have h_lhs : polymerFreeEnergy G t = 0 := by
    unfold polymerFreeEnergy
    rw [h_vd, Finset.sum_singleton, Finset.prod_empty, Real.log_one]
  have h_rhs : mayerPartialSum G N t = 0 := by
    unfold mayerPartialSum
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rcases n with _ | k
    · exact mayerExpansionTerm_zero G t
    · unfold mayerExpansionTerm
      refine Finset.sum_eq_zero (fun ω hω => ?_)
      rw [Fintype.mem_piFinset] at hω
      have h0 : ω 0 ∈ allPolymers G := hω 0
      rw [h_no] at h0
      exact absurd h0 (Finset.notMem_empty _)
  rw [h_lhs, h_rhs]

/-- **Mayer identity tanh form for empty-polymer graphs** (Step 619):
restate Step 618 in `tanh(β·J)` form. -/
theorem mayer_identity_of_no_polymers_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers G h_no _ N

/-- **Mayer identity holds under disjunctive trivial conditions** (Step 651):
`polymerFreeEnergy G (tanh(β·J)) = mayerPartialSum G N (tanh(β·J))`
holds when either `β·J = 0` (so `tanh = 0`, both sides reduce to 0)
or `allPolymers G = ∅` (so both sides equal 0 via vanishing). -/
theorem mayer_identity_of_trivial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (h : β * J = 0 ∨ allPolymers G = ∅) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  rcases h with hβJ | hno
  · exact polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G hβJ N
  · exact mayer_identity_of_no_polymers_tanh G hno β J N

/-- **Mayer identity at `J = 0`** (Step 652 specialisation). -/
theorem mayer_identity_at_J_zero_polymer_free_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  mayer_identity_of_trivial G (Or.inl (mul_zero β)) N

/-- **Mayer identity at `β = 0`** (Step 652 specialisation). -/
theorem mayer_identity_at_beta_zero_polymer_free_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * J)) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  mayer_identity_of_trivial G (Or.inl (zero_mul J)) N

/-- **Mayer identity at `J = 0` and `β = 0`** (Step 653): both
specialisations bundled. -/
theorem mayer_identity_at_either_zero_polymer_free_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  mayer_identity_of_trivial G (Or.inl (mul_zero 0)) N

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G t` under `t ≥ 0`**
(Step 654): trivially `mayerPartialSum G 0 t = 0` (Step 592) and
`0 ≤ polymerFreeEnergy G t` (via `Real.log_nonneg` + Step 605). -/
theorem mayerPartialSum_zero_le_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    mayerPartialSum G 0 t ≤ polymerFreeEnergy G t := by
  rw [mayerPartialSum_zero]
  unfold polymerFreeEnergy
  exact Real.log_nonneg (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G (tanh(β·J))` under
`0 ≤ β·J`** (Step 655). -/
theorem mayerPartialSum_zero_tanh_le_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    mayerPartialSum G 0 (Real.tanh (β * J)) ≤
      polymerFreeEnergy G (Real.tanh (β * J)) :=
  mayerPartialSum_zero_le_polymerFreeEnergy G (real_tanh_nonneg hβJ)

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G (tanh(β·J))`
ferromagnetic** (Step 656). -/
theorem mayerPartialSum_zero_tanh_le_polymerFreeEnergy_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    mayerPartialSum G 0 (Real.tanh (β * J)) ≤
      polymerFreeEnergy G (Real.tanh (β * J)) :=
  mayerPartialSum_zero_tanh_le_polymerFreeEnergy G (mul_nonneg hβ.le hJ)

/-- **`vdPolymerFamilies_sum` split as 1 + (Γ ≠ ∅) contribution**
(Step 657, Mayer general-t Phase A): writing
`vdSum G t = 1 + ε(t)` where `ε(t) = ∑_{Γ ∈ vdCompat, Γ ≠ ∅} ∏ t^|P|`.
Foundation for `log(1+ε)` Taylor expansion via Mayer combinatorics. -/
theorem vdPolymerFamilies_sum_eq_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  rw [show vdCompatiblePolymerFamilies G =
        insert (∅ : Finset (Finset (Sym2 ι)))
          ((vdCompatiblePolymerFamilies G).erase ∅) from
        (Finset.insert_erase h_empty_in).symm,
      Finset.sum_insert (Finset.notMem_erase _ _),
      Finset.prod_empty,
      Finset.erase_insert (Finset.notMem_erase _ _)]

/-- **`allPolymers G = ∅` when `G` has no edges** (Step 620): an
edgeless graph has no even subgraph other than `∅`, which is excluded
from `IsPolymer` by the non-emptiness clause. -/
theorem allPolymers_eq_empty_of_edgeFinset_empty
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) :
    allPolymers G = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_allPolymers] at hP
  -- IsPolymer G P ⇒ P ⊆ G.edgeFinset (= ∅) and P.Nonempty
  obtain ⟨e, heP⟩ := hP.nonempty
  have h_e : e ∈ G.edgeFinset := hP.isEven.subset heP
  rw [h_empty] at h_e
  exact absurd h_e (Finset.notMem_empty _)

/-- **Mayer identity for edgeless graphs** (Step 620): when
`G.edgeFinset = ∅`, the Mayer identity `polymerFreeEnergy G t =
mayerPartialSum G N t` holds for every `t` and `N`. Combines
Step 620's `allPolymers = ∅` with Step 618. -/
theorem mayer_identity_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t :=
  mayer_identity_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, `polymerFreeEnergy G t = 0` for every `t`,
since `vdCompatiblePolymerFamilies G = {∅}` and `log 1 = 0`. -/
theorem polymerFreeEnergy_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 := by
  rw [mayer_identity_of_no_polymers G h_no t 0, mayerPartialSum_zero]

/-- **`mayerPartialSum = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, every Mayer term vanishes (no polymer
sequences exist for `n ≥ 1`; n=0 vanishes via Step 587). -/
theorem mayerPartialSum_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 := by
  rw [← mayer_identity_of_no_polymers G h_no t N,
      polymerFreeEnergy_eq_zero_of_no_polymers G h_no t]

/-- **Edgeless-graph Mayer identity in tanh form** (Step 622): lift
Step 620 to the `tanh(β·J)` argument. -/
theorem mayer_identity_of_edgeFinset_empty_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty G h_empty _ N

/-- **`polymerFreeEnergy = 0` for edgeless graphs** (Step 623). -/
theorem polymerFreeEnergy_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 :=
  polymerFreeEnergy_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t

/-- **`mayerPartialSum = 0` for edgeless graphs** (Step 623). -/
theorem mayerPartialSum_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 :=
  mayerPartialSum_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy` DifferentiableOn `[0, ∞)`** (Step 626):
lift Step 610's per-point AnalyticAt to DifferentiableOn over the
half-line. -/
theorem polymerFreeEnergy_differentiableOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).differentiableAt).differentiableWithinAt

/-- **`polymerFreeEnergy` ContinuousOn `[0, ∞)`** (Step 627). -/
theorem polymerFreeEnergy_continuousOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ContinuousOn (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).continuousAt).continuousWithinAt

/-- **`mayerPartialSum` ContinuousOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_continuousOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_continuous G N).continuousOn

/-- **`mayerPartialSum` DifferentiableOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_differentiableOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_differentiable G N).differentiableOn

/-- **vdPolymerFamilies sum sandwich for `t ≥ 0`** (Step 631):
`1 ≤ vdSum G t ≤ (1+t)^|E|`. Combines Step 605 (≥ 1) with Step 629
(≤ (1+t)^|E|). -/
theorem vdPolymerFamilies_sum_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
  ⟨vdPolymerFamilies_sum_ge_one_of_nonneg G ht,
   vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht⟩

/-- **`polymerFreeEnergy ≤ |E| · log(1+t)` under `t ≥ 0`** (Step 630):
apply `Real.log_le_log` to Step 629's bound `vdSum ≤ (1+t)^|E|`. The
right-hand side `Real.log ((1+t)^|E|) = |E| · log(1+t)` via `Real.log_pow`. -/
theorem polymerFreeEnergy_le_card_log_one_plus_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) := by
  unfold polymerFreeEnergy
  have h_pos : 0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G,
      ∏ P ∈ Γ, t ^ P.card :=
    vdPolymerFamilies_sum_pos_of_nonneg G ht
  have h_le : (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
    vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht
  calc Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      ≤ Real.log ((1 + t) ^ G.edgeFinset.card) :=
            Real.log_le_log h_pos h_le
    _ = G.edgeFinset.card * Real.log (1 + t) := by
            rw [Real.log_pow]

/-- **`polymerFreeEnergy ≥ 0` under `t ≥ 0`** (Step 631): direct
consequence of Step 605 (`vdSum ≥ 1`) and `Real.log_nonneg`. -/
theorem polymerFreeEnergy_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t :=
  Real.log_nonneg (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`polymerFreeEnergy` sandwich for `t ≥ 0`** (Step 631):
`0 ≤ polymerFreeEnergy G t ≤ |E| · log(1 + t)`. -/
theorem polymerFreeEnergy_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t ∧
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) :=
  ⟨polymerFreeEnergy_nonneg_of_nonneg G ht,
   polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht⟩

/-- **`polymerFreeEnergy` sandwich at `tanh(β·J)`** (Step 632): tanh-form
restatement of Step 631. Under `0 ≤ β·J`, `0 ≤ Real.tanh (β·J)`, so
the sandwich applies. -/
theorem polymerFreeEnergy_tanh_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_sandwich_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`vdPolymerFamilies_sum` is monotone on `[0, ∞)`** (Step 633):
each term `t^|X|` is monotone in `t` for `t ≥ 0`, so the sum is too. -/
theorem vdPolymerFamilies_sum_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) := by
  intro t ht s hs hts
  refine Finset.sum_le_sum (fun Γ _ => ?_)
  refine Finset.prod_le_prod (fun P _ => pow_nonneg ht _) (fun P _ => ?_)
  exact pow_le_pow_left₀ ht hts _

/-- **`polymerFreeEnergy` is monotone on `[0, ∞)`** (Step 633): apply
`Real.log_le_log` to `vdSum` monotonicity. -/
theorem polymerFreeEnergy_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ => polymerFreeEnergy G t) (Set.Ici 0) := by
  intro t ht s hs hts
  unfold polymerFreeEnergy
  exact Real.log_le_log (vdPolymerFamilies_sum_pos_of_nonneg G ht)
    (vdPolymerFamilies_sum_monotoneOn_Ici_zero G ht hs hts)

/-- **`polymerFreeEnergy` preserves order on `[0, ∞)`** (Step 649):
direct order-preservation corollary of Step 633 (monotonicity). -/
theorem polymerFreeEnergy_le_of_le_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    polymerFreeEnergy G t ≤ polymerFreeEnergy G s :=
  polymerFreeEnergy_monotoneOn_Ici_zero G ht hs hts

/-- **`polymerFreeEnergy` strict monotonicity-style at `t > 0`**
(Step 650): for any `0 ≤ t ≤ s`, `polymerFreeEnergy G t ≤
polymerFreeEnergy G s`. Trivial corollary of Step 649; serves as a
75-PR milestone marker for the §18.4 Mayer infrastructure
(Steps 576-650). -/
theorem polymerFreeEnergy_le_of_le_strict_form
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    polymerFreeEnergy G t ≤ polymerFreeEnergy G s :=
  polymerFreeEnergy_le_of_le_of_nonneg G ht (le_trans ht hts) hts

/-- **`polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`** (Step 634):
sharpen Step 630 via `Real.log_le_sub_one_of_pos` (i.e. `log(1+t) ≤ t`). -/
theorem polymerFreeEnergy_le_card_mul_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * t := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h_pos : (0 : ℝ) < 1 + t := by linarith
  have := Real.log_le_sub_one_of_pos h_pos
  linarith

/-- **`polymerFreeEnergy ≤ |E|·tanh(β·J)` under `0 ≤ β·J`** (Step 635):
tanh form of Step 634. -/
theorem polymerFreeEnergy_tanh_le_card_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_le_card_mul_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_sandwich`** (Step 636):
under `0 ≤ J, 0 < β`. -/
theorem polymerFreeEnergy_tanh_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_tanh_sandwich G (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_le_card_mul`** (Step 636). -/
theorem polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_tanh_le_card_mul G (mul_nonneg hβ.le hJ)

/-- **`mayerExpansionTerm G 1 t ≥ 0` under `t ≥ 0`** (Step 637):
the n=1 Mayer term equals `∑_P t^|P|`, all non-negative. -/
theorem mayerExpansionTerm_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mayerExpansionTerm G 1 t := by
  rw [mayerExpansionTerm_one]
  exact Finset.sum_nonneg (fun P _ => pow_nonneg ht _)

/-- **`vdPolymerFamilies_sum` at `t = 1`** (Step 639): every product
`∏ 1^|P| = 1`, so the sum collapses to the cardinality of
`vdCompatiblePolymerFamilies G`. -/
theorem vdPolymerFamilies_sum_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (vdCompatiblePolymerFamilies G).card := by
  classical
  have h_each : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      (∏ P ∈ Γ, (1 : ℝ) ^ P.card) = 1 := by
    intro Γ _
    refine Finset.prod_eq_one (fun P _ => ?_)
    exact one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy` at `t = 1`** (Step 640): equals
`log |vdCompatiblePolymerFamilies G|`. Direct via Step 639. -/
theorem polymerFreeEnergy_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 1 =
      Real.log (vdCompatiblePolymerFamilies G).card := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_one]

/-- **`mayerPartialSum G 1 t = |allPolymers G|` at `t = 1`** (Step 641):
each polymer contributes `1^|P| = 1`, so the sum equals the number of
polymers. -/
theorem mayerPartialSum_one_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    mayerPartialSum G 1 1 = (allPolymers G).card := by
  classical
  rw [mayerPartialSum_one]
  have h_each : ∀ P ∈ allPolymers G, (1 : ℝ) ^ P.card = 1 := fun _ _ => one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy ≤ |E| · log 2` for `0 ≤ t ≤ 1`** (Step 642):
under `t ≤ 1`, `log(1+t) ≤ log 2`. -/
theorem polymerFreeEnergy_le_card_log_two_of_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log 2 := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Real.log_le_log (by linarith) (by linarith)

/-- **`polymerFreeEnergy_tanh ≤ |E| · log 2` under `0 ≤ β·J`** (Step 643):
since `tanh(β·J) < 1` always, Step 642 applies. -/
theorem polymerFreeEnergy_tanh_le_card_log_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_le_card_log_two_of_le_one G (real_tanh_nonneg hβJ)
    (Real.tanh_lt_one _).le

/-- **Ferromagnetic `polymerFreeEnergy_tanh ≤ |E| · log 2`** (Step 644). -/
theorem polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_tanh_le_card_log_two G (mul_nonneg hβ.le hJ)

/-- **`polymerFreeEnergy_tanh` double bound** (Step 645): under
`0 ≤ β·J`, both `polymerFreeEnergy_tanh ≤ |E|·tanh(β·J)` (Step 635)
and `≤ |E|·log 2` (Step 643) hold simultaneously. -/
theorem polymerFreeEnergy_tanh_double_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  ⟨polymerFreeEnergy_tanh_le_card_mul G hβJ,
   polymerFreeEnergy_tanh_le_card_log_two G hβJ⟩

/-- **`mayerPartialSum` recurrence in `N`** (Step 638):
`mayerPartialSum G (N+1) t = mayerPartialSum G N t + mayerExpansionTerm G (N+1) t`. -/
theorem mayerPartialSum_succ
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerPartialSum G (N + 1) t =
      mayerPartialSum G N t + mayerExpansionTerm G (N + 1) t := by
  unfold mayerPartialSum
  rw [show ((N + 1) + 1) = (N + 1) + 1 from rfl, Finset.sum_range_succ]

/-- **`mayerExpansionTerm = mayerPartialSum` diff** (Step 646):
rearrangement of Step 638. -/
theorem mayerExpansionTerm_eq_mayerPartialSum_diff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerExpansionTerm G (N + 1) t =
      mayerPartialSum G (N + 1) t - mayerPartialSum G N t := by
  rw [mayerPartialSum_succ]
  ring

/-- **`mayerExpansionTerm G 2 t ≤ 0` under `t ≥ 0`** (Step 637):
the n=2 Mayer term equals `-1/2 · ∑_{(P,Q) incompat} t^|P|·t^|Q|`,
non-positive. Matches the alternating sign of log(1+x) Taylor
coefficients. -/
theorem mayerExpansionTerm_two_nonpos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    mayerExpansionTerm G 2 t ≤ 0 := by
  rw [mayerExpansionTerm_two_filter]
  refine mul_nonpos_of_nonpos_of_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg (fun pq _ => ?_)
  exact mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)

/-- **`polymerFreeEnergy` HasDerivAt** (Step 625): explicit derivative
of `polymerFreeEnergy G t = Real.log (vdPolymerFamilies_sum G t)` via
the log-derivative formula `(log f)' = f' / f`. The derivative of
`vdPolymerFamilies_sum G` is given by Step 575 (explicit polynomial
form), and positivity (Step 605) ensures `f t ≠ 0`. -/
theorem polymerFreeEnergy_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => polymerFreeEnergy G s)
      ((∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)) t := by
  unfold polymerFreeEnergy
  exact (vdPolymerFamilies_sum_hasDerivAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht).ne'

/-- **`freeEnergy = log 2` at `β·J = 0`** (Step 624): when `β·J = 0`,
the Step 612 decomposition reduces to `f = log 2` since
`cosh(0) = 1`, `log 1 = 0`, and `polymerFreeEnergy G (tanh 0) = 0`
(Step 600). Recovers the well-known free-energy value at trivial
slices. -/
theorem freeEnergy_eq_log_two_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ = Real.log 2 := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β (hβJ.symm ▸ le_refl 0) hne, hβJ,
      Real.cosh_zero, Real.log_one, Real.tanh_zero,
      polymerFreeEnergy_at_zero, mul_zero, zero_div, add_zero, add_zero]

/-- **`polymerFreeEnergy = log(1 + ε)` form** (Step 658, Mayer
general-t Phase A): rewrite `polymerFreeEnergy G t` as
`Real.log (1 + ε(t))` where `ε(t) = ∑_{Γ ≠ ∅} ∏ t^|P|`. Foundation
for Taylor expansion `log(1+ε) = ∑_n (-1)^(n-1)/n · ε^n` for `|ε| < 1`. -/
theorem polymerFreeEnergy_eq_log_one_add_eps
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    polymerFreeEnergy G t =
      Real.log (1 + ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_eq_one_add]

/-- **`ε(0) = 0`** (Step 659, Mayer general-t Phase A): every Γ ≠ ∅
in `vdCompatiblePolymerFamilies` contains a polymer P with |P| ≥ 1,
so 0^|P| = 0 and the product vanishes. -/
theorem vdPolymerFamilies_sum_minus_one_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
  rw [Finset.mem_erase] at hΓ
  obtain ⟨h_ne, h_in⟩ := hΓ
  obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
  rw [mem_vdCompatiblePolymerFamilies] at h_in
  have hP_polymer : IsPolymer G P := mem_allPolymers.mp (h_in.1 hP)
  have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
  exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')

/-- **`ε(t) ≥ 0` for `t ≥ 0`** (Step 660, Mayer general-t Phase A):
each summand is a finite product of non-negative terms `t^|P|`. -/
theorem vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card := by
  refine Finset.sum_nonneg (fun _ _ => ?_)
  exact Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)

/-- **`ε(t) ≤ (1+t)^|E| - 1` for `t ≥ 0`** (Step 661, Mayer general-t
Phase A): subtract 1 from Step 629's `vdSum ≤ (1+t)^|E|` after using
the Step 657 split. -/
theorem vdPolymerFamilies_sum_minus_one_le_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) ≤ (1 + t) ^ G.edgeFinset.card - 1 := by
  have h_le := vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht
  rw [vdPolymerFamilies_sum_eq_one_add] at h_le
  linarith

/-- **`ε(t)` is continuous** (Step 662, Mayer general-t Phase A):
finite sum of finite products of monomials in `t`. -/
theorem vdPolymerFamilies_sum_minus_one_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ (fun Γ _ => ?_)
  refine continuous_finset_prod _ (fun P _ => ?_)
  exact continuous_id.pow _

/-- **`ε(t)` is analyticAt every `t`** (Step 663, Mayer general-t
Phase A): finite sum of analytic terms via `analyticAt_prod_pow`. -/
theorem vdPolymerFamilies_sum_minus_one_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t := by
  refine Finset.analyticAt_fun_sum _ (fun Γ _ => analyticAt_prod_pow Γ t)

/-- **`ε(t) → 0` as `t → 0`** (Step 664, Mayer general-t Phase A):
combine continuity (Step 662) with `ε(0) = 0` (Step 659) to get
the limit at `t = 0`. -/
theorem vdPolymerFamilies_sum_minus_one_tendsto_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) := by
  have h_cont := (vdPolymerFamilies_sum_minus_one_continuous G).continuousAt (x := 0)
  rw [ContinuousAt, vdPolymerFamilies_sum_minus_one_at_zero] at h_cont
  exact h_cont

/-- **`ε(t) < 1` eventually as `t → 0`** (Step 665, Mayer general-t
Phase A): since ε is continuous and ε(0) = 0, in some nbhd of 0,
ε(t) < 1 (the threshold for `log(1+ε)` Taylor convergence). -/
theorem vdPolymerFamilies_sum_minus_one_lt_one_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) < 1 := by
  exact (vdPolymerFamilies_sum_minus_one_tendsto_zero G).eventually_lt_const zero_lt_one

/-- **ε(t)^n at t=0 for n ≥ 1** (Step 668, Mayer general-t Phase A):
since `ε(0) = 0` and `0^n = 0` for `n ≥ 1`, every `n`-th power
vanishes at t=0. -/
theorem vdPolymerFamilies_sum_minus_one_pow_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 := by
  rw [vdPolymerFamilies_sum_minus_one_at_zero]
  exact zero_pow (by omega : n ≠ 0)

/-- **ε(t)^n expansion as sum over Γ-tuples** (Step 667, Mayer
general-t Phase A): apply `Finset.sum_pow'` to express
  ε(t)^n = ∑_{(Γ_1, ..., Γ_n) ∈ piFinset (vdCompat.erase ∅)^n}
            ∏_i ∏_{P ∈ Γ_i} t^|P|.
This is the multi-Γ-tuple expansion needed to combine with
log(1+x) Taylor series (Step 666). -/
theorem vdPolymerFamilies_sum_minus_one_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => (vdCompatiblePolymerFamilies G).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  Finset.sum_pow' _ _ n

/-- **`Real.log(1+x)` power series for `|x| < 1`** (Step 666, Mayer
general-t Phase A): wrapper of Mathlib's `hasSum_pow_div_log_of_abs_lt_one`
applied at `-x`, giving
  HasSum (fun n => (-1)^n · x^(n+1) / (n+1)) (Real.log (1 + x))

This is the standard alternating-sign log(1+x) Taylor series, which
matches the n-th order Mayer-expansion contribution structure. -/
theorem hasSum_real_log_one_add_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1))
      (Real.log (1 + x)) := by
  have h_neg : |(-x)| < 1 := by rwa [abs_neg]
  have h_base : HasSum (fun n : ℕ => (-x) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - -x)) := Real.hasSum_pow_div_log_of_abs_lt_one h_neg
  rw [show ((1 : ℝ) - -x) = 1 + x from by ring] at h_base
  have h' := h_base.neg
  rw [neg_neg] at h'
  convert h' using 1
  funext n
  have h_neg_pow : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by
    rw [pow_succ]; ring
  rw [show ((-x : ℝ) ^ (n + 1)) = (-1) ^ (n + 1) * x ^ (n + 1) from by ring,
      h_neg_pow]
  ring

/-- **polymerFreeEnergy power series via log(1+ε) Taylor**: when
`|ε(t)| < 1`, the polymer free energy admits a convergent series
representation
  polymerFreeEnergy G t = ∑_{n ≥ 0} (-1)^n · ε(t)^(n+1) / (n+1)
where `ε(t) = ∑_{Γ ≠ ∅} ∏ t^|P|`. This connects Mayer-side
combinatorial sums to the analytic log Taylor series.

Bundles together the ε-power expansion (Step 667), log(1+x) Taylor
(Step 666), and `polymerFreeEnergy = log(1+ε)` (Step 658). The full
Mayer identity (matching this sum to a polymer-sequence sum via
Mayer combinatorial identity for `K_n` connected subgraphs)
remains deferred; this lemma provides the analytic side. -/
theorem polymerFreeEnergy_hasSum_via_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
                       ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G t) := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  exact hasSum_real_log_one_add_of_abs_lt_one h_abs

/-- **polymerFreeEnergy series convergence eventually** (companion
bundle): in some neighbourhood of `t = 0`, the convergent log(1+ε)
representation holds. -/
theorem polymerFreeEnergy_hasSum_via_log_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (polymerFreeEnergy G t) := by
  have h_abs_tendsto :
      Filter.Tendsto (fun t : ℝ =>
        |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card|) (nhds 0) (nhds 0) := by
    have h := vdPolymerFamilies_sum_minus_one_tendsto_zero G
    simpa using (Continuous.tendsto continuous_abs (0 : ℝ)).comp h
  have h_abs_lt : ∀ᶠ t : ℝ in nhds 0,
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card| < 1 :=
    h_abs_tendsto.eventually_lt_const zero_lt_one
  exact h_abs_lt.mono (fun t h => polymerFreeEnergy_hasSum_via_log G h)

/-- **Explicit convergence radius for Mayer log expansion**: under
`0 ≤ t` with `(1 + t) ^ |E(G)| < 2`, the polymer free energy admits
the convergent series representation
  polymerFreeEnergy G t = ∑_{n ≥ 0} (-1)^n · ε(t)^(n+1) / (n+1).

Combines Step 661 (`ε(t) ≤ (1+t)^|E| - 1`) and Step 660 (`ε(t) ≥ 0`)
to derive `|ε(t)| < 1`, then applies `polymerFreeEnergy_hasSum_via_log`. -/
theorem polymerFreeEnergy_hasSum_via_log_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (h_pow : (1 + t) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G t) := by
  have h_eps_nonneg := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have h_eps_le := vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht
  have h_eps_lt_one :
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card| < 1 := by
    rw [abs_of_nonneg h_eps_nonneg]
    linarith
  exact polymerFreeEnergy_hasSum_via_log G h_eps_lt_one

/-- **`polymerFreeEnergy` log-Taylor expansion (tanh form)** (§18.5
GJ-命題-bundle): tanh-substituted version of
`polymerFreeEnergy_hasSum_via_log_of_pow_lt_two` for the
ferromagnetic Ising activity `t = tanh(β·J)` under `0 ≤ β·J` and
`(1 + tanh(β·J))^|E| < 2`. -/
theorem polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G (Real.tanh (β * J))) :=
  polymerFreeEnergy_hasSum_via_log_of_pow_lt_two G
    (real_tanh_nonneg hβJ) h_pow

/-- **`polymerFreeEnergy` log-Taylor expansion (ferromagnetic tanh
form)** (§18.5 ferromagnetic): under `0 ≤ J, 0 < β` and
`(1 + tanh(β·J))^|E| < 2`, same `HasSum` log-Taylor expansion. -/
theorem polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G (Real.tanh (β * J))) :=
  polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two G
    (mul_nonneg hβ.le hJ) h_pow


end IsingModel
