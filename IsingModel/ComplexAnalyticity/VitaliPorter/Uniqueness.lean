import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ClusterPt

/-!
# Vitali–Porter: the uniqueness (identity-theorem) core

This is the first building block of an in-project proof of the Vitali–Porter convergence theorem
(`vitaliPorter_tendstoLocallyUniformlyOn`, currently a declared scope-excluded axiom —
Issue #4280). It isolates the **uniqueness** half: two holomorphic functions
on an open preconnected set `U` that agree with the same function `g` on a subset `S` having an
accumulation point in `U` must agree on all of `U`.

This is a direct consequence of the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`). It is the step that, in the full
Vitali–Porter argument, forces every locally-uniform subsequential limit of a locally bounded
holomorphic family to be the *same* function (hence the whole sequence converges), once
normal-family (Montel) compactness has supplied the subsequential limits.

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2–3 (Vitali's theorem). -/

namespace IsingModel
namespace FunctionTheory

open Filter Topology

/-- **Vitali–Porter uniqueness core (identity theorem)**.

Let `U ⊆ ℂ` be open and preconnected, `f₁, f₂ : ℂ → ℂ` holomorphic on `U`, and `S ⊆ U` a set with
an accumulation point `z₀ ∈ U` (`AccPt z₀ (𝓟 S)`). If both `f₁` and `f₂` agree with a function `g`
on `S`, then they agree on all of `U`.

Proof: `S` accumulating at `z₀` means `f₁ = f₂` (both `= g`) frequently in the punctured
neighbourhood filter `𝓝[≠] z₀`, so the identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (via `DifferentiableOn.analyticOnNhd`) gives
`EqOn f₁ f₂ U`. -/
theorem vitali_uniqueness
    {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    {f₁ f₂ : ℂ → ℂ} (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    {S : Set ℂ} (_hSU : S ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hacc : AccPt z₀ (Filter.principal S))
    {g : ℂ → ℂ} (hf₁S : Set.EqOn f₁ g S) (hf₂S : Set.EqOn f₂ g S) :
    Set.EqOn f₁ f₂ U := by
  have a1 : AnalyticOnNhd ℂ f₁ U := hf₁.analyticOnNhd hU
  have a2 : AnalyticOnNhd ℂ f₂ U := hf₂.analyticOnNhd hU
  -- `S` accumulates at `z₀`: frequently in `𝓝 z₀` we meet `S` away from `z₀`.
  rw [accPt_iff_frequently] at hacc
  -- Transport to: `f₁ = f₂` frequently in the punctured neighbourhood filter.
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f₁ z = f₂ z := by
    rw [frequently_nhdsWithin_iff]
    refine hacc.mono ?_
    rintro y ⟨hy_ne, hyS⟩
    exact ⟨(hf₁S hyS).trans (hf₂S hyS).symm, by simpa using hy_ne⟩
  exact a1.eqOn_of_preconnected_of_frequently_eq a2 hUconn hz₀ hfreq

/-- **Uniqueness of a locally-uniform limit identified on an accumulating subset**.

Specialisation phrased for the Vitali–Porter assembly: if two candidate limits `f₁, f₂` are
holomorphic on `U` and both restrict to the *pointwise limit* `g` on the accumulating subset `S`,
they coincide on `U`. (Same statement as `vitali_uniqueness`, exposed under the name the
normal-family compactness step will consume.) -/
theorem subsequential_limit_unique
    {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    {f₁ f₂ g : ℂ → ℂ} (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    {S : Set ℂ} (_hSU : S ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hacc : AccPt z₀ (Filter.principal S))
    (hf₁S : Set.EqOn f₁ g S) (hf₂S : Set.EqOn f₂ g S) :
    Set.EqOn f₁ f₂ U :=
  vitali_uniqueness hU hUconn hf₁ hf₂ _hSU hz₀ hacc hf₁S hf₂S

end FunctionTheory
end IsingModel
