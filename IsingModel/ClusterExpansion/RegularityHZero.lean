import IsingModel.ClusterExpansion.Families.SandwichBounds

/-!
# Cluster expansion zero-field regularity wrappers

Mechanical child split from `ClusterExpansion.lean`.
-/

namespace IsingModel

open Finset
open scoped Topology

/-- **Lattice Ising polymer partition function**: the polymer model
partition function `polymerPartition` evaluated at the universe of all
polymers in `G` with the canonical activity `tanh(β·J)^|P|`. This is
the polymer-decomposition reformulation of the FV (3.45) sum
`∑_{X ⊆ E, even} tanh(β·J)^|X|` modulo the connected-components
identification (proved in subsequent PRs). -/
noncomputable def latticeIsingPolymerPartition {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) : ℝ :=
  polymerPartition G (allPolymers G) (polymerActivity (Real.tanh (β * J)))

/-- **Polymer activity at non-negative `t` is non-negative**: with
`t = tanh(β·J)`, this gives `0 ≤ tanh(β·J)^|P|` whenever `0 ≤ β·J`. -/
theorem polymerActivity_nonneg {ι : Type*} {t : ℝ} (ht : 0 ≤ t)
    (P : Finset (Sym2 ι)) : 0 ≤ polymerActivity t P := by
  unfold polymerActivity
  exact pow_nonneg ht _

/-- **Lattice Ising polymer partition function ≥ 1 under `0 ≤ β·J`**:
since `0 ≤ β·J` implies `0 ≤ tanh(β·J)`, the activity is non-negative
and the empty family contributes exactly 1. -/
theorem latticeIsingPolymerPartition_ge_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ latticeIsingPolymerPartition G β J := by
  have h_tanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  unfold latticeIsingPolymerPartition
  apply polymerPartition_ge_one G _
  intro P _
  exact polymerActivity_nonneg h_tanh_nn P

/-- **Polymer activity is `1` on the empty edge set** (since `t^0 = 1`). -/
@[simp]
theorem polymerActivity_empty (t : ℝ) :
    polymerActivity t (∅ : Finset (Sym2 ι)) = 1 := by
  unfold polymerActivity
  simp

/-- **VD polymer-family sum is continuous in `t`**: the sum
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} t^|P|`
is a finite sum of finite products of monomials `t^|P|`, hence continuous
(and indeed polynomial) in `t : ℝ`. This is the foundation for the §18.6
analyticity of the polymer expansion in `tanh(β·J)`. -/
theorem vdPolymerFamilies_sum_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ ?_
  intro Γ _
  refine continuous_finset_prod _ ?_
  intro P _
  exact continuous_id.pow _

/-- **VD polymer-family sum is differentiable in `t`**: as a finite sum
of finite products of monomials `t^|P|`, the polymer-family sum is a
polynomial in `t`, hence differentiable on all of `ℝ`. Strengthens
`vdPolymerFamilies_sum_continuous` from `Continuous` to `Differentiable`
and prepares the §18.6 analyticity statement. -/
theorem vdPolymerFamilies_sum_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine Differentiable.fun_sum (fun Γ _ => ?_)
  refine Differentiable.fun_finset_prod (fun P _ => ?_)
  exact (differentiable_id (𝕜 := ℝ)).pow _

/-- **`Real.tanh` is continuous on `ℝ`** (project-local helper): derived
from `tanh = sinh / cosh` together with `Real.cosh > 0`. Mathlib does
not yet export `Real.continuous_tanh`, so we provide it here. -/
theorem continuous_real_tanh : Continuous Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.continuous_sinh.div Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **`Real.tanh` is differentiable on `ℝ`** (project-local helper):
derived from `tanh = sinh / cosh` together with `Real.cosh > 0` and
`Differentiable.div`. Mathlib does not yet export `Real.differentiable_tanh`. -/
theorem differentiable_real_tanh : Differentiable ℝ Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.differentiable_sinh.div Real.differentiable_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **VD polymer-family sum is continuous in `β` (with `J` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is continuous in `J` (with `β` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `β` (with `J` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.mul_const`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `J` (with `β` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.const_mul`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **Partition function continuous in `β` (at `h = 0`) via polymer
expansion**: combines the §18.4 polymer-family identity (Step 548) with
the polymer-family sum continuity (Step 556) and continuity of
`cosh(β·J)^|E|` to obtain
`Continuous (fun β => partitionFunction G ⟨J, 0, β⟩)`.

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three β-continuous factors. -/
theorem partitionFunction_continuous_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_beta G J)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function continuous in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_continuous_beta_h_zero` for the
coupling variable, again via the polymer-family identity. The general
form for non-zero `h` is `partitionFunction_continuous_J` in
`GibbsMeasure.lean`; this `_h_zero` version goes through the polymer
expansion and so will be the natural place to extend to higher
regularity (e.g. analyticity) in subsequent steps. -/
theorem partitionFunction_continuous_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_J G β)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `β` (at `h = 0`) via polymer
expansion**: strengthens `partitionFunction_continuous_beta_h_zero` from
`Continuous` to `Differentiable ℝ`, using Step 559 plus differentiability
of `cosh(β·J)^|E|` (composition of `Real.differentiable_cosh` and
`Differentiable.mul_const`, raised to the power `|E|`).

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three differentiable factors. -/
theorem partitionFunction_differentiable_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_beta G J)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_differentiable_beta_h_zero` for
the coupling variable. Strengthens `partitionFunction_continuous_J_h_zero`
from `Continuous` to `Differentiable ℝ`. -/
theorem partitionFunction_differentiable_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_J G β)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

/-- **Real-analytic version of `Finset.prod` of monomials**: for any
finite set `Γ : Finset (Finset (Sym2 ι))`, the function
`fun t : ℝ => ∏ P ∈ Γ, t ^ P.card` is real-analytic at every point.
Proof by `Finset.induction` on `Γ`. -/
theorem analyticAt_prod_pow
    {ι : Type*} (Γ : Finset (Finset (Sym2 ι))) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) t)
  | insert P Γ hP ih =>
      have h_step : (fun s : ℝ => ∏ P' ∈ insert P Γ, s ^ P'.card) =
          (fun s : ℝ => s ^ P.card * ∏ P' ∈ Γ, s ^ P'.card) := by
        funext s
        exact Finset.prod_insert hP
      rw [h_step]
      exact (analyticAt_id.pow P.card).mul ih

/-- **VD polymer-family sum is real-analytic in `t`**: at every `t : ℝ`,
the polymer-family sum is a polynomial in `t` and hence real-analytic.
Proof by `Finset.induction` on `vdCompatiblePolymerFamilies G` using
`analyticAt_prod_pow`. Strengthens Step 558 (`Differentiable`) to
`AnalyticAt ℝ`. -/
theorem vdPolymerFamilies_sum_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction (vdCompatiblePolymerFamilies G) using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) t)
  | insert Γ S hΓ ih =>
      have h_step : (fun s : ℝ => ∑ Γ' ∈ insert Γ S, ∏ P ∈ Γ', s ^ P.card) =
          (fun s : ℝ => (∏ P ∈ Γ, s ^ P.card) +
            ∑ Γ' ∈ S, ∏ P ∈ Γ', s ^ P.card) := by
        funext s
        exact Finset.sum_insert hΓ
      rw [h_step]
      exact (analyticAt_prod_pow Γ t).add ih

/-- **`Real.tanh` is real-analytic at every point** (project-local helper):
derived from `tanh = sinh / cosh` together with `Real.cosh > 0` and
`AnalyticAt.div`. Mathlib does not yet export `Real.analyticAt_tanh`. -/
theorem analyticAt_real_tanh (x : ℝ) : AnalyticAt ℝ Real.tanh x := by
  have h_eq : Real.tanh = fun y : ℝ => Real.sinh y / Real.cosh y :=
    funext (fun y => Real.tanh_eq_sinh_div_cosh y)
  rw [h_eq]
  exact AnalyticAt.div Real.analyticAt_sinh Real.analyticAt_cosh
    (Real.cosh_pos x).ne'

/-- **VD polymer-family sum is real-analytic in `β` (with `J` fixed)**:
chain-rule composition of Step 561 with `analyticAt_real_tanh` and the
analytic linear factor `β ↦ β * J`. -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β := by
  have h_mul : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  exact (vdPolymerFamilies_sum_analyticAt G _).comp
    ((analyticAt_real_tanh _).comp h_mul)

/-- **VD polymer-family sum is real-analytic in `J` (with `β` fixed)**:
chain-rule composition of Step 561 with `analyticAt_real_tanh` and the
analytic linear factor `J ↦ β * J`. -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J := by
  have h_mul : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  exact (vdPolymerFamilies_sum_analyticAt G _).comp
    ((analyticAt_real_tanh _).comp h_mul)

/-- **Partition function `AnalyticAt ℝ` in `β` (at `h = 0`) via polymer
expansion**: combines the §18.4 polymer-family identity (Step 548) with
Step 562 (polymer-family sum `AnalyticAt`) and `Real.analyticAt_cosh` to
obtain `AnalyticAt ℝ (fun β => partitionFunction G ⟨J, 0, β⟩) β`.
Strengthens `partitionFunction_differentiable_beta_h_zero` from
`Differentiable ℝ` to `AnalyticAt ℝ`. -/
theorem partitionFunction_analyticAt_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) β := by
  have h_eq : (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) =
      fun β' : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β' * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : AnalyticAt ℝ (fun β' : ℝ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  refine AnalyticAt.mul ?_ (vdPolymerFamilies_sum_tanh_analyticAt_beta G J β)
  refine analyticAt_const.mul ?_
  exact ((Real.analyticAt_cosh).comp h_mul).pow _

/-- **Partition function `AnalyticAt ℝ` in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_analyticAt_beta_h_zero`. -/
theorem partitionFunction_analyticAt_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) J := by
  have h_eq : (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) =
      fun J' : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J') ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card :=
    funext (fun J' => partitionFunction_high_temp_expansion_h_zero_polymer_family G J' β)
  rw [h_eq]
  have h_mul : AnalyticAt ℝ (fun J' : ℝ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  refine AnalyticAt.mul ?_ (vdPolymerFamilies_sum_tanh_analyticAt_J G β J)
  refine analyticAt_const.mul ?_
  exact ((Real.analyticAt_cosh).comp h_mul).pow _

/-- **Free energy `AnalyticAt ℝ` in `β` (at `h = 0`) via polymer
expansion**: composes `partitionFunction_analyticAt_beta_h_zero` (Step 563)
with `AnalyticAt.log` (using `partitionFunction_pos` to discharge the
positivity hypothesis) and the constant `1/|ι|` factor.

The free energy `f = (1/|ι|) · log Z` is therefore real-analytic in `β`
at every point. Completes the §18.6 free-energy analyticity capstone at
`h = 0`. -/
theorem freeEnergy_analyticAt_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergy G ⟨J, 0, β'⟩) β := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_beta_h_zero G J β).log
    (partitionFunction_pos G _)

/-- **Free energy `AnalyticAt ℝ` in `J` (at `h = 0`) via polymer
expansion**: dual of `freeEnergy_analyticAt_beta_h_zero`. -/
theorem freeEnergy_analyticAt_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergy G ⟨J', 0, β⟩) J := by
  unfold freeEnergy
  refine analyticAt_const.mul ?_
  exact (partitionFunction_analyticAt_J_h_zero G β J).log
    (partitionFunction_pos G _)

/-- **Partition function `AnalyticOnNhd ℝ _ Set.univ` in `β` (at `h = 0`)**:
strengthens `partitionFunction_analyticAt_beta_h_zero` (Step 563) from
per-point `AnalyticAt` to a global `AnalyticOnNhd ℝ _ Set.univ` statement. -/
theorem partitionFunction_analyticOnNhd_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => partitionFunction G ⟨J, 0, β'⟩) Set.univ :=
  fun β _ => partitionFunction_analyticAt_beta_h_zero G J β

/-- **Partition function `AnalyticOnNhd ℝ _ Set.univ` in `J` (at `h = 0`)**:
dual of `partitionFunction_analyticOnNhd_beta_h_zero`. -/
theorem partitionFunction_analyticOnNhd_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => partitionFunction G ⟨J', 0, β⟩) Set.univ :=
  fun J _ => partitionFunction_analyticAt_J_h_zero G β J

/-- **Free energy `AnalyticOnNhd ℝ _ Set.univ` in `β` (at `h = 0`)**:
strengthens `freeEnergy_analyticAt_beta_h_zero` (Step 564) from per-point
`AnalyticAt` to a global `AnalyticOnNhd ℝ _ Set.univ` statement. Completes
the §18.6 capstone in its global form at `h = 0`. -/
theorem freeEnergy_analyticOnNhd_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => freeEnergy G ⟨J, 0, β'⟩) Set.univ :=
  fun β _ => freeEnergy_analyticAt_beta_h_zero G J β

/-- **Free energy `AnalyticOnNhd ℝ _ Set.univ` in `J` (at `h = 0`)**:
dual of `freeEnergy_analyticOnNhd_beta_h_zero`. -/
theorem freeEnergy_analyticOnNhd_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => freeEnergy G ⟨J', 0, β⟩) Set.univ :=
  fun J _ => freeEnergy_analyticAt_J_h_zero G β J

/-- **VD polymer-family sum is continuous in `t : ℂ`** (Issue #3054). The same
polynomial in `t` as `vdPolymerFamilies_sum_continuous`, viewed as a function `ℂ → ℂ`.
Foundation for the §18.6 complex analyticity of the polymer expansion. -/
theorem vdPolymerFamilies_sum_continuous_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ ?_
  intro Γ _
  refine continuous_finset_prod _ ?_
  intro P _
  exact continuous_id.pow _

/-- **VD polymer-family sum is `Differentiable ℂ` in `t`** (Issue #3054). A polynomial in
`t : ℂ`, hence complex-differentiable everywhere. Strengthens
`vdPolymerFamilies_sum_continuous_complex` and prepares the complex analyticity
statement. -/
theorem vdPolymerFamilies_sum_differentiable_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℂ (fun t : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine Differentiable.fun_sum (fun Γ _ => ?_)
  refine Differentiable.fun_finset_prod (fun P _ => ?_)
  exact (differentiable_id (𝕜 := ℂ)).pow _

/-- **Complex-analytic factored product `∏ s^|P|`** (Issue #3054): induction helper
mirroring `analyticAt_prod_pow` for `t : ℂ`. -/
theorem analyticAt_prod_pow_complex
    {ι : Type*} (Γ : Finset (Finset (Sym2 ι))) (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) t)
  | insert P Γ hP ih =>
      have h_step : (fun s : ℂ => ∏ P' ∈ insert P Γ, s ^ P'.card) =
          (fun s : ℂ => s ^ P.card * ∏ P' ∈ Γ, s ^ P'.card) := by
        funext s
        exact Finset.prod_insert hP
      rw [h_step]
      exact (analyticAt_id.pow P.card).mul ih

/-- **VD polymer-family sum is `AnalyticAt ℂ`** (Issue #3054). A polynomial in `t : ℂ`,
hence complex-analytic at every point. The foundational complex extension of the real
analyticity `vdPolymerFamilies_sum_analyticAt` (§18.6), first step in extending the
cluster expansion to a complex `β`/`J` disc for the volume-uniform `Z_ℂ` lower bound
(Lemma 17.5.2 hZ provider, Issue #3044 / Issue #3026). -/
theorem vdPolymerFamilies_sum_analyticAt_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) t := by
  classical
  induction (vdCompatiblePolymerFamilies G) using Finset.induction_on with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) t)
  | insert Γ S hΓ ih =>
      have h_step : (fun s : ℂ => ∑ Γ' ∈ insert Γ S, ∏ P ∈ Γ', s ^ P.card) =
          (fun s : ℂ => (∏ P ∈ Γ, s ^ P.card) +
            ∑ Γ' ∈ S, ∏ P ∈ Γ', s ^ P.card) := by
        funext s
        exact Finset.sum_insert hΓ
      rw [h_step]
      exact (analyticAt_prod_pow_complex Γ t).add ih

/-- **`Complex.tanh` is `AnalyticAt ℂ` where `cosh ≠ 0`** (Issue #3054, project-local
helper). Rewrite via `Complex.tanh_eq_sinh_div_cosh` and `AnalyticAt.div` of the entire
`Complex.sinh` and `Complex.cosh` (`Complex.analyticOnNhd_sinh / _cosh`). Provides the
complex-`tanh` analyticity for the cluster-expansion complex extension — the relevant
substitution is `Complex.tanh ((β·J : ℂ))` in the polymer expansion. -/
theorem analyticAt_complex_tanh (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    AnalyticAt ℂ Complex.tanh z := by
  change AnalyticAt ℂ (fun w : ℂ => Complex.sinh w / Complex.cosh w) z
  have hsinh : AnalyticAt ℂ Complex.sinh z :=
    Complex.analyticOnNhd_sinh (s := Set.univ) z (Set.mem_univ _)
  have hcosh : AnalyticAt ℂ Complex.cosh z :=
    Complex.analyticOnNhd_cosh (s := Set.univ) z (Set.mem_univ _)
  exact hsinh.div hcosh hz

/-- **VD polymer-family sum (complex), substituted at `tanh(β·J)` is `AnalyticAt ℂ` in
`β`** (Issue #3054). Chain-rule composition of `vdPolymerFamilies_sum_analyticAt_complex`
with `analyticAt_complex_tanh` and the entire linear factor `β ↦ β * J`. The polymer
expansion in the complex cluster-expansion regime uses the substitution
`t := Complex.tanh ((β · J : ℂ))`; this lemma exhibits the resulting compound
`β ↦ ∑_Γ ∏_{P∈Γ} (Complex.tanh (β·J))^|P|` as complex-analytic at every `β` with
`Complex.cosh (β·J) ≠ 0`. Complex analogue of `vdPolymerFamilies_sum_tanh_analyticAt_beta`
(§18.6). -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_complex_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℂ)
    (hcosh : Complex.cosh (β * J) ≠ 0) :
    AnalyticAt ℂ (fun β' : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh (β' * J) ^ P.card) β := by
  have h_mul : AnalyticAt ℂ (fun β' : ℂ => β' * J) β :=
    analyticAt_id.mul analyticAt_const
  have h_tanh : AnalyticAt ℂ (Complex.tanh ∘ (fun β' : ℂ => β' * J)) β := by
    refine AnalyticAt.comp ?_ h_mul
    exact analyticAt_complex_tanh _ hcosh
  have h_final : AnalyticAt ℂ ((fun s : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) ∘
        (Complex.tanh ∘ (fun β' : ℂ => β' * J))) β :=
    (vdPolymerFamilies_sum_analyticAt_complex G _).comp h_tanh
  exact h_final

/-- **VD polymer-family sum (complex), substituted at `tanh(β·J)` is `AnalyticAt ℂ` in
`J`** (Issue #3054). Chain-rule composition of `vdPolymerFamilies_sum_analyticAt_complex`
with `analyticAt_complex_tanh` and the entire linear factor `J ↦ β * J`. Complex analogue
of `vdPolymerFamilies_sum_tanh_analyticAt_J` (§18.6). -/
theorem vdPolymerFamilies_sum_tanh_analyticAt_complex_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℂ)
    (hcosh : Complex.cosh (β * J) ≠ 0) :
    AnalyticAt ℂ (fun J' : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh (β * J') ^ P.card) J := by
  have h_mul : AnalyticAt ℂ (fun J' : ℂ => β * J') J :=
    analyticAt_const.mul analyticAt_id
  have h_tanh : AnalyticAt ℂ (Complex.tanh ∘ (fun J' : ℂ => β * J')) J := by
    refine AnalyticAt.comp ?_ h_mul
    exact analyticAt_complex_tanh _ hcosh
  have h_final : AnalyticAt ℂ ((fun s : ℂ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, s ^ P.card) ∘
        (Complex.tanh ∘ (fun J' : ℂ => β * J'))) J :=
    (vdPolymerFamilies_sum_analyticAt_complex G _).comp h_tanh
  exact h_final

/-- **Polymer-family sum (complex) at `t = 0`** (Issue #3054): the
`∑_Γ ∏_P t^|P|` evaluated at the complex zero equals `1`. Mirror of
`vdPolymerFamilies_sum_at_zero` — only the empty family `Γ = ∅` contributes
(its empty product equals `1`); any non-empty `Γ` contains a polymer with
`|P| ≥ 1`, so `(0 : ℂ)^|P| = 0` and the product vanishes. Provides the
constant term of the polymer-family sum at `t = 0`, the foundational point for
local non-vanishing of the polymer expansion in a complex disc (en route to the
volume-uniform `Z_ℂ` lower bound for the Lemma 17.5.2 `hZ` provider, Issue
#3044). -/
theorem vdPolymerFamilies_sum_complex_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, (0 : ℂ) ^ P.card) = 1 := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  have h_nonempty_zero : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      Γ ≠ ∅ → (∏ P ∈ Γ, (0 : ℂ) ^ P.card) = 0 := by
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

/-- **Polymer-family sum with `Complex.tanh` evaluated at `β = 0` equals `1`**
(Issue #3054): immediate from `Complex.tanh_zero` (`tanh 0 = 0`) and
`vdPolymerFamilies_sum_complex_at_zero`. -/
theorem vdPolymerFamilies_sum_tanh_complex_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh ((0 : ℂ) * J) ^ P.card) = 1 := by
  simp [Complex.tanh_zero, vdPolymerFamilies_sum_complex_at_zero]

/-- **Polymer-family sum with `Complex.tanh` is eventually non-zero near
`β = 0`** (Issue #3054). At `β = 0` the sum equals `1` (via
`vdPolymerFamilies_sum_tanh_complex_at_zero_beta`); by complex-analytic continuity
(`vdPolymerFamilies_sum_tanh_analyticAt_complex_beta`, using `Complex.cosh 0 = 1
≠ 0`), the sum stays non-zero in a complex neighborhood of `β = 0`. The complex
analogue of the local non-vanishing point for the polymer expansion — the first
step in the eventual zero-free disc for the volume-uniform `Z_ℂ` lower bound of
the Lemma 17.5.2 `hZ` provider (#3044). -/
theorem vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∀ᶠ β : ℂ in 𝓝 (0 : ℂ),
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have hcosh0 : Complex.cosh ((0 : ℂ) * J) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_analyticAt :
      AnalyticAt ℂ (fun β : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 :=
    vdPolymerFamilies_sum_tanh_analyticAt_complex_beta G J 0 hcosh0
  have h_continuousAt := h_analyticAt.continuousAt
  have h_at_zero :
      (fun β : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 = 1 :=
    vdPolymerFamilies_sum_tanh_complex_at_zero_beta G J
  have h_ne : (fun β : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 ≠ 0 := by
    rw [h_at_zero]; exact one_ne_zero
  exact h_continuousAt.eventually_ne h_ne

/-- **Polymer-family sum with `Complex.tanh` is non-zero on a complex ball at
`β = 0`** (Issue #3054). Quantitative ball-form of
`vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta`: there
exists a radius `r > 0` such that the `tanh`-substituted complex polymer-family
sum is non-zero on the entire `Metric.ball (0 : ℂ) r`. Derived from
`Metric.eventually_nhds_iff_ball` applied to the `Eventually` form. The radius
`r` depends on `G` and `J`; volume-uniformity is the next step. -/
theorem vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∃ r > 0, ∀ β ∈ Metric.ball (0 : ℂ) r,
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have h := vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta G J
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨r, hr_pos, hr⟩ := h
  exact ⟨r, hr_pos, hr⟩

/-- **Polymer-family sum with `Complex.tanh` is bounded below by `ε > 0` on a
closed complex ball at `β = 0`** (Issue #3054). Compactness + continuity
upgrade of the ball-form non-vanishing
`vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta`: pick a
strictly smaller closed sub-ball, where the continuous norm function attains
its minimum (which is `> 0` since the sum is non-zero on the larger open ball).

The dependence of both `r` and `ε` on `G`/`J` is not yet quantified — this is
the per-fixed-volume version. Volume-uniformity is the open hard core for the
Lemma 17.5.2 `hZ` provider (Issue #3044). -/
theorem vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℂ) :
    ∃ r > 0, ∃ ε > 0, ∀ β ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖ := by
  classical
  -- Open ball where polymer-tanh sum is non-zero (#3060).
  obtain ⟨r₁, hr₁, h_ne⟩ :=
    vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta G J
  -- Open ball where cosh (β·J) ≠ 0 (needed for tanh continuity).
  have hcont_cosh : Continuous (fun β : ℂ => Complex.cosh (β * J)) :=
    Complex.continuous_cosh.comp (continuous_id.mul continuous_const)
  have h_cosh0 : Complex.cosh ((0 : ℂ) * J) ≠ 0 := by
    rw [zero_mul, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ β in 𝓝 (0 : ℂ), Complex.cosh (β * J) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r₂, hr₂, h_cosh_ne⟩ := h_cosh_ev
  -- Take r := min(r₁, r₂) / 2 so closedBall (0) r ⊂ ball (0) r₁ ∩ ball (0) r₂.
  set r : ℝ := min r₁ r₂ / 2 with hr_def
  have hr_pos : 0 < r := by
    have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  have hmin_pos : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hr_lt_r1 : r < r₁ := by
    have : min r₁ r₂ ≤ r₁ := min_le_left _ _
    simp only [hr_def]; linarith
  have hr_lt_r2 : r < r₂ := by
    have : min r₁ r₂ ≤ r₂ := min_le_right _ _
    simp only [hr_def]; linarith
  have h_sub_b1 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₁ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  have h_sub_b2 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₂ := by
    intro β hβ
    rw [Metric.mem_closedBall] at hβ
    rw [Metric.mem_ball]; linarith
  -- Continuity of `Complex.tanh (β·J)` on closedBall (0) r.
  have h_tanh_cont :
      ContinuousOn (fun β : ℂ => Complex.tanh (β * J))
        (Metric.closedBall (0 : ℂ) r) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Complex.continuous_sinh.comp
        (continuous_id.mul continuous_const)).continuousOn
    · exact hcont_cosh.continuousOn
    · intro β hβ
      exact h_cosh_ne β (h_sub_b2 hβ)
  -- Continuity of the polymer-tanh sum on closedBall.
  have h_sum_cont :
      ContinuousOn (fun β : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card)
        (Metric.closedBall (0 : ℂ) r) :=
    continuousOn_finset_sum _ (fun Γ _ =>
      continuousOn_finset_prod _ (fun P _ => h_tanh_cont.pow _))
  have h_norm_cont :
      ContinuousOn (fun β : ℂ =>
        ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖)
        (Metric.closedBall (0 : ℂ) r) :=
    h_sum_cont.norm
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall _ _
  have h_nonempty : (Metric.closedBall (0 : ℂ) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr_pos.le⟩
  obtain ⟨β_min, hβ_min, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cont
  set ε := ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β_min * J) ^ P.card‖
  have h_ne_val : ∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β_min * J) ^ P.card ≠ 0 :=
    h_ne β_min (h_sub_b1 hβ_min)
  have h_eps_pos : 0 < ε := norm_pos_iff.mpr h_ne_val
  refine ⟨ε, h_eps_pos, ?_⟩
  intro β hβ
  exact h_min hβ

/-- **Polymer-family sum with `Complex.tanh` evaluated at `J = 0` equals `1`**
(Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_at_zero_beta`): immediate from
`Complex.tanh_zero` (`tanh (β · 0) = tanh 0 = 0`) and
`vdPolymerFamilies_sum_complex_at_zero`. -/
theorem vdPolymerFamilies_sum_tanh_complex_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Complex.tanh (β * (0 : ℂ)) ^ P.card) = 1 := by
  simp [Complex.tanh_zero, vdPolymerFamilies_sum_complex_at_zero]

/-- **Polymer-family sum with `Complex.tanh` is eventually non-zero near `J = 0`**
(Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∀ᶠ J : ℂ in 𝓝 (0 : ℂ),
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have hcosh0 : Complex.cosh (β * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, Complex.cosh_zero]; exact one_ne_zero
  have h_analyticAt :
      AnalyticAt ℂ (fun J : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 :=
    vdPolymerFamilies_sum_tanh_analyticAt_complex_J G β 0 hcosh0
  have h_continuousAt := h_analyticAt.continuousAt
  have h_at_zero :
      (fun J : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 = 1 :=
    vdPolymerFamilies_sum_tanh_complex_at_zero_J G β
  have h_ne : (fun J : ℂ => ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) 0 ≠ 0 := by
    rw [h_at_zero]; exact one_ne_zero
  exact h_continuousAt.eventually_ne h_ne

/-- **Polymer-family sum with `Complex.tanh` is non-zero on a complex ball at
`J = 0`** (Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∃ r > 0, ∀ J ∈ Metric.ball (0 : ℂ) r,
      (∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card) ≠ 0 := by
  have h := vdPolymerFamilies_sum_tanh_complex_eventually_ne_zero_at_zero_J G β
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨r, hr_pos, hr⟩ := h
  exact ⟨r, hr_pos, hr⟩

/-- **Polymer-family sum with `Complex.tanh` is bounded below by `ε > 0` on a
closed complex ball at `J = 0`** (Issue #3054, `J`-direction analogue of
`vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_beta`). -/
theorem vdPolymerFamilies_sum_tanh_complex_norm_ge_eps_on_closedBall_at_zero_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℂ) :
    ∃ r > 0, ∃ ε > 0, ∀ J ∈ Metric.closedBall (0 : ℂ) r,
      ε ≤ ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
         ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖ := by
  classical
  obtain ⟨r₁, hr₁, h_ne⟩ :=
    vdPolymerFamilies_sum_tanh_complex_ne_zero_on_ball_at_zero_J G β
  have hcont_cosh : Continuous (fun J : ℂ => Complex.cosh (β * J)) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  have h_cosh0 : Complex.cosh (β * (0 : ℂ)) ≠ 0 := by
    rw [mul_zero, Complex.cosh_zero]; exact one_ne_zero
  have h_cosh_ev : ∀ᶠ J in 𝓝 (0 : ℂ), Complex.cosh (β * J) ≠ 0 :=
    hcont_cosh.continuousAt.eventually_ne h_cosh0
  rw [Metric.eventually_nhds_iff_ball] at h_cosh_ev
  obtain ⟨r₂, hr₂, h_cosh_ne⟩ := h_cosh_ev
  set r : ℝ := min r₁ r₂ / 2 with hr_def
  have hr_pos : 0 < r := by
    have : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    simp only [hr_def]; linarith
  refine ⟨r, hr_pos, ?_⟩
  have hmin_pos : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hr_lt_r1 : r < r₁ := by
    have : min r₁ r₂ ≤ r₁ := min_le_left _ _
    simp only [hr_def]; linarith
  have hr_lt_r2 : r < r₂ := by
    have : min r₁ r₂ ≤ r₂ := min_le_right _ _
    simp only [hr_def]; linarith
  have h_sub_b1 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₁ := by
    intro J hJ
    rw [Metric.mem_closedBall] at hJ
    rw [Metric.mem_ball]; linarith
  have h_sub_b2 : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r₂ := by
    intro J hJ
    rw [Metric.mem_closedBall] at hJ
    rw [Metric.mem_ball]; linarith
  have h_tanh_cont :
      ContinuousOn (fun J : ℂ => Complex.tanh (β * J))
        (Metric.closedBall (0 : ℂ) r) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Complex.continuous_sinh.comp
        (continuous_const.mul continuous_id)).continuousOn
    · exact hcont_cosh.continuousOn
    · intro J hJ
      exact h_cosh_ne J (h_sub_b2 hJ)
  have h_sum_cont :
      ContinuousOn (fun J : ℂ =>
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card)
        (Metric.closedBall (0 : ℂ) r) :=
    continuousOn_finset_sum _ (fun Γ _ =>
      continuousOn_finset_prod _ (fun P _ => h_tanh_cont.pow _))
  have h_norm_cont :
      ContinuousOn (fun J : ℂ =>
        ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
            ∏ P ∈ Γ, Complex.tanh (β * J) ^ P.card‖)
        (Metric.closedBall (0 : ℂ) r) :=
    h_sum_cont.norm
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall _ _
  have h_nonempty : (Metric.closedBall (0 : ℂ) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr_pos.le⟩
  obtain ⟨J_min, hJ_min, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty h_norm_cont
  set ε := ‖∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β * J_min) ^ P.card‖
  have h_ne_val : ∑ Γ ∈ vdCompatiblePolymerFamilies G,
       ∏ P ∈ Γ, Complex.tanh (β * J_min) ^ P.card ≠ 0 :=
    h_ne J_min (h_sub_b1 hJ_min)
  have h_eps_pos : 0 < ε := norm_pos_iff.mpr h_ne_val
  refine ⟨ε, h_eps_pos, ?_⟩
  intro J hJ
  exact h_min hJ

end IsingModel
