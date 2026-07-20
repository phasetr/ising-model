import IsingModel.ClusterExpansion.Families.SandwichBounds

/-!
# Cluster expansion zero-field regularity (2/4): real analyticity capstone

Structural split (2/4) of `ClusterExpansion.RegularityHZero`.  This child holds the
real-analyticity chain of the §18.6 zero-field cluster expansion: the monomial-product
helper `analyticAt_prod_pow`, the `AnalyticAt ℝ` statements for the vertex-disjoint
polymer-family sum (in `t`, and in `β` / `J` through `tanh(β·J)`), and the resulting
`AnalyticAt ℝ` / `AnalyticOnNhd ℝ _ Set.univ` statements for the partition function and
the free energy at `h = 0`.  It builds on the continuity and differentiability layer in
the sibling `...PolymerSumContinuityDifferentiability`.  See the
`ClusterExpansion.RegularityHZero` facade module for the full contents overview.
-/

namespace IsingModel

open Finset
open scoped Topology

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

end IsingModel
