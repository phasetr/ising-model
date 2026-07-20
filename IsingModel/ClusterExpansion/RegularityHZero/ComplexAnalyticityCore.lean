import IsingModel.ClusterExpansion.Families.SandwichBounds

/-!
# Cluster expansion zero-field regularity (3/4): complex analyticity core

Structural split (3/4) of `ClusterExpansion.RegularityHZero`.  This child holds the
complex counterparts of the polymer-family sum regularity (Issue #3054): continuity and
`Differentiable ℂ` in the activity variable `t : ℂ`, the monomial-product helper
`analyticAt_prod_pow_complex`, the `AnalyticAt ℂ` polymer-family sum, the project-local
`analyticAt_complex_tanh`, and the `tanh`-substituted `AnalyticAt ℂ` statements in `β`
and `J`.  The zero-free ball consequences live in the sibling `...ComplexZeroFreeBalls`.
See the `ClusterExpansion.RegularityHZero` facade module for the full contents overview.
-/

namespace IsingModel

open Finset
open scoped Topology

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

end IsingModel
