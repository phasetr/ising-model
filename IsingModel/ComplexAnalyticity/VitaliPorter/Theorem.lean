import IsingModel.ComplexAnalyticity.VitaliPorter.MontelExtraction
import IsingModel.ComplexAnalyticity.VitaliPorter.Uniqueness
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Vitali–Porter convergence theorem (proved)

This file **proves** the Vitali–Porter convergence theorem
`vitaliPorter_tendstoLocallyUniformlyOn`, previously a declared scope-excluded axiom (Issue #4280).
It combines the complex Montel theorem (`MontelExtraction.lean`) with the identity-theorem
uniqueness core (`Uniqueness.lean`):

* Montel gives **one** locally-uniformly convergent subsequence with holomorphic limit `f`; the
  pointwise hypothesis on the accumulating set `S` identifies `f` with `g` on `S`.
* The **whole** sequence then converges: by the subsequence-uniqueness principle
  (`tendsto_of_subseq_tendsto` in the compact-convergence space `C(↥U, ℂ)`), every subsequence has a
  further Montel subsequence whose limit again agrees with `g` on `S`, hence equals `f` by the
  identity theorem; so all subsequential limits coincide and the sequence converges to `f`.

Proving this removes the `vitaliPorter_tendstoLocallyUniformlyOn` axiom from the project.

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2–3 (Montel / Vitali). -/

namespace IsingModel
namespace FunctionTheory

open Filter Topology Set

/-- **Vitali–Porter convergence theorem** (classical complex analysis; proved here).

Let `U ⊆ ℂ` be open and preconnected, `F n` holomorphic on `U`, the family locally uniformly
bounded, and `F n` convergent pointwise to `g` on a subset `S ⊆ U` with an accumulation point
`z₀ ∈ U`. Then
`F n` converges **locally uniformly** on `U` to a holomorphic `f` agreeing with `g` on `S`. -/
theorem vitaliPorter_tendstoLocallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z r, ‖F n w‖ ≤ M)
    {S : Set ℂ} (hSU : S ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hacc : AccPt z₀ (Filter.principal S))
    {g : ℂ → ℂ} (hpt : ∀ z ∈ S, Filter.Tendsto (fun n => F n z) Filter.atTop (nhds (g z))) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn F f Filter.atTop U ∧ Set.EqOn f g S := by
  classical
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SigmaCompactSpace U := by infer_instance
  -- Local boundedness transports to any subsequence.
  have hbddSub : ∀ (σ : ℕ → ℕ), ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ Metric.ball z r, ‖F (σ n) w‖ ≤ M := by
    intro σ z hz
    obtain ⟨r, M, hr, hball, hb⟩ := hbdd z hz
    exact ⟨r, M, hr, hball, fun n w hw => hb (σ n) w hw⟩
  -- Any subsequence has a Montel-convergent sub-subsequence whose limit agrees with `g` on `S`.
  have hmontel : ∀ (σ : ℕ → ℕ), Tendsto σ atTop atTop → ∃ (ms : ℕ → ℕ) (f' : ℂ → ℂ),
      StrictMono ms ∧ DifferentiableOn ℂ f' U ∧
      TendstoLocallyUniformlyOn (fun j => F (σ (ms j))) f' atTop U ∧ Set.EqOn f' g S := by
    intro σ hσ
    obtain ⟨ms, hms, f', hf'_diff, hf'_loc⟩ :=
      exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded hU
        (fun k => hF (σ k)) (hbddSub σ)
    refine ⟨ms, f', hms, hf'_diff, hf'_loc, ?_⟩
    intro z hz
    have h1 : Tendsto (fun j => F (σ (ms j)) z) atTop (𝓝 (f' z)) := hf'_loc.tendsto_at (hSU hz)
    have h2 : Tendsto (fun j => F (σ (ms j)) z) atTop (𝓝 (g z)) :=
      (hpt z hz).comp (hσ.comp hms.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  -- The base limit `f` from `σ = id`.
  obtain ⟨ms₀, f, _hms₀, hf_diff, hf_loc, hf_eqS⟩ := hmontel id tendsto_id
  refine ⟨f, hf_diff, ?_, hf_eqS⟩
  -- Whole-sequence convergence via subsequence uniqueness in `C(↥U, ℂ)`.
  have hf_cont : ContinuousOn f U := hf_diff.continuousOn
  let xfun : ℕ → C(U, ℂ) := fun n => ⟨U.restrict (F n), ((hF n).continuousOn).restrict⟩
  let afun : C(U, ℂ) := ⟨U.restrict f, hf_cont.restrict⟩
  -- Coercions agree with the `comp_coe` form of locally uniform convergence.
  have hxcoe : ∀ n, (⇑(xfun n) : U → ℂ) = (fun a : U => F n ↑a) := fun _ => rfl
  have hacoe : (⇑afun : U → ℂ) = (fun a : U => f ↑a) := rfl
  have htend : Tendsto xfun atTop (𝓝 afun) := by
    refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
    obtain ⟨ms, f', _hms, _hf'_diff, hf'_loc, hf'_eqS⟩ := hmontel ns hns
    -- `f' = f` on `U` by the identity theorem.
    have hf'f : Set.EqOn f' f U :=
      vitali_uniqueness hU hUconn _hf'_diff hf_diff hSU hz₀ hacc hf'_eqS hf_eqS
    refine ⟨ms, ?_⟩
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    have hloc : TendstoLocallyUniformlyOn (fun j => F (ns (ms j))) f atTop U :=
      hf'_loc.congr_right hf'f
    have hbridge := (tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe
      (F := fun j => F (ns (ms j))) (f := f) (p := atTop) (s := U)).mp hloc
    exact hbridge
  -- Read off locally uniform convergence on `U` from `C(↥U, ℂ)`-convergence.
  have hfinal := (ContinuousMap.tendsto_iff_tendstoLocallyUniformly
    (F := xfun) (f := afun) (p := atTop)).mp htend
  exact (tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe
    (F := F) (f := f) (p := atTop) (s := U)).mpr hfinal

end FunctionTheory
end IsingModel
