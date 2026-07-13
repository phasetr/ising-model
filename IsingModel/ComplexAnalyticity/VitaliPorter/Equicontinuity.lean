import IsingModel.Analysis.HolomorphicEquicontinuity
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Vitali–Porter: Montel equicontinuity from local boundedness (Cauchy estimates)

Second building block of the in-project proof eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). It supplies the **Montel** half's
equicontinuity input: a locally uniformly bounded family of holomorphic functions is locally
equicontinuous.

This is now a thin `DifferentiableOn` wrapper over the shared holomorphic-equicontinuity core
`IsingModel.equicontinuousAt_of_analyticOnNhd_of_ballBound` (Issue #4501): on ℂ, holomorphy on an
open set is analyticity (`DifferentiableOn.analyticOnNhd`), so the `ℕ`-indexed `DifferentiableOn`
family is fed into the general `AnalyticOnNhd` core.

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2 (normal families / Montel). -/

namespace IsingModel
namespace FunctionTheory

open Complex Metric Set

/-- **Equicontinuity at a point from a local uniform bound** (Montel input, ball form).

If every `F n` is holomorphic on the open `U`, `ball x₀ ρ ⊆ U` (`ρ > 0`), and `‖F n w‖ ≤ M` for all
`n` and `w ∈ ball x₀ ρ`, then the family `F` is equicontinuous at `x₀`.

Thin wrapper: holomorphy on the open `U` upgrades to `AnalyticOnNhd` via
`DifferentiableOn.analyticOnNhd`, restricted to `ball x₀ ρ`; the shared core
`equicontinuousAt_of_analyticOnNhd_of_ballBound` then supplies the common modulus of continuity. -/
theorem equicontinuousAt_of_ball_bound
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    {x₀ : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hballU : ball x₀ ρ ⊆ U)
    (hbound : ∀ n, ∀ w ∈ ball x₀ ρ, ‖F n w‖ ≤ M) :
    EquicontinuousAt (fun n => F n) x₀ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbound 0 x₀ (Metric.mem_ball_self hρ))
  have hana : ∀ n, AnalyticOnNhd ℂ (F n) (ball x₀ ρ) :=
    fun n => ((hF n).analyticOnNhd hU).mono hballU
  exact equicontinuousAt_of_analyticOnNhd_of_ballBound hρ hM0 hana hbound

/-- **Equicontinuity at a point from the local-boundedness hypothesis** (Montel input).

Existential-`ball` repackaging of `equicontinuousAt_of_ball_bound`: from the local uniform bound
`∃ r M, 0 < r ∧ ball x₀ r ⊆ U ∧ ∀ n w ∈ ball x₀ r, ‖F n w‖ ≤ M` (the standard "locally uniformly
bounded family" hypothesis at `x₀`), the holomorphic family `F` is equicontinuous at `x₀`. -/
theorem equicontinuousAt_of_locallyBounded
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) {x₀ : ℂ}
    (hbdd : ∃ r M : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∀ n, ∀ w ∈ ball x₀ r, ‖F n w‖ ≤ M) :
    EquicontinuousAt (fun n => F n) x₀ := by
  obtain ⟨r, M, hr, hrU, hbound⟩ := hbdd
  exact equicontinuousAt_of_ball_bound hU hF hr hrU hbound

end FunctionTheory
end IsingModel
