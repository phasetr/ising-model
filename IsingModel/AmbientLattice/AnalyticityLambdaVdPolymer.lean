import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.ZeroBounds

/-!
# Regularity of the polymer sum and of its logarithm (§18.5-§18.6)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Write `Ξ t` for the polymer sum
`∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ), ∏ P ∈ Γ, t ^ P.card`; it has no
definition of its own, is written out in every statement, and only the theorem names
abbreviate it to `vdPolymerFamilies_sum_Λ`.

`Ξ` is a finite sum of monomials in the activity, and its statements say so with no region
excluded: `Continuous` and `Differentiable ℝ` on all of `ℝ`, `AnalyticAt ℝ` at an arbitrary
real point, and `HasDerivAt` at an arbitrary point with the derivative named explicitly as
`∑ Γ, ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) * (Q.card * t ^ (Q.card - 1))`. Composed with
`Real.tanh (β * J)` and read in `β` with `J` frozen, or in `J` with `β` frozen, it is again
`Continuous`, `Differentiable ℝ` and `AnalyticAt ℝ` at an arbitrary point, with no sign
condition on the parameters.

`Real.log (Ξ t)` is where the region starts to matter, since `Ξ` is `1` at `t = 0` and at
least `1` only once `0 ≤ t`. Its statements are therefore `AnalyticAt ℝ` at a point `t`
assumed to satisfy `0 ≤ t`, `AnalyticOnNhd ℝ` over `Set.Ici 0`, and — in the `Real.tanh`
composition — `AnalyticAt ℝ` in `β` and in `J` under `0 ≤ β * J`. Nothing here treats a
negative activity, in either direction.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `0 ≤ t` and `0 ≤ β * J`; every statement about `Ξ` itself carries neither.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 vdPolymerFamilies_sum regularity in t Λ wraps -/

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Continuous` in `t`** (§18.6). -/
theorem vdPolymerFamilies_sum_Λ_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_continuous (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Differentiable ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_differentiable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_differentiable (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `AnalyticAt ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) t

/-- **Λ-layer: `vdPolymerFamilies_sum` `HasDerivAt` (explicit
polynomial derivative)**. -/
theorem vdPolymerFamilies_sum_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  IsingModel.vdPolymerFamilies_sum_hasDerivAt (inducedGraph G Λ) t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_beta (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_J (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_beta
    (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_J
    (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J

/-! ### §18.5 log_vdPolymerFamilies_sum analyticity Λ wraps -/

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) t :=
  IsingModel.log_vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticOnNhd over `[0, ∞)`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  IsingModel.log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    (inducedGraph G Λ)

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β hβJ

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J hβJ


end Ambient

end IsingModel
