import IsingModel.ComplexAnalyticity.VitaliPorter.Equicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Vitali–Porter: Arzelà–Ascoli subsequence on a single compact set

Fourth building block toward eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). On a **single compact** `K ⊆ U`, a family of
functions that is continuous on `U`, equicontinuous at each point of `U`, and uniformly bounded on
`K` admits a subsequence converging **uniformly on `K`** (the per-compact Arzelà–Ascoli extraction).

This packages `BoundedContinuousFunction.arzela_ascoli` (relative compactness of the restricted
family in `↥K →ᵇ ℂ`) with `IsCompact.tendsto_subseq` (sequential compactness) and the
`↥K →ᵇ ℂ`-convergence ↔ `TendstoUniformlyOn K` dictionary.

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2 (Montel / normal families). -/

namespace IsingModel
namespace FunctionTheory

open Filter Topology Metric BoundedContinuousFunction

/-- **Per-compact Arzelà–Ascoli subsequence extraction**.

If each `F n` is continuous on the open `U`, the family is equicontinuous at every point of `U`, and
uniformly bounded by `M` on a compact `K ⊆ U`, then some subsequence of `F` converges uniformly on
`K` to a limit `g : ℂ → ℂ`.

Proof: restrict to the bounded continuous functions `f n : ↥K →ᵇ ℂ`; the values lie in the compact
`closedBall 0 M` and the family is equicontinuous on the compact subtype `↥K`, so
`BoundedContinuousFunction.arzela_ascoli` makes `closure (range f)` compact;
`IsCompact.tendsto_subseq` extracts a convergent subsequence in `↥K →ᵇ ℂ`, which is uniform
convergence on `↥K` (`tendsto_iff_tendstoUniformly`); transporting along `Subtype.val`
(`tendstoUniformlyOn_iff_tendstoUniformly_comp_coe`) gives `TendstoUniformlyOn … K`, with the limit
extended to `ℂ` by `Function.extend`. -/
theorem exists_subseq_tendstoUniformlyOn_compact
    {U : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, ContinuousOn (F n) U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hequi : ∀ x ∈ U, EquicontinuousAt (fun n => F n) x)
    {M : ℝ} (hbdd : ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (φ k)) g atTop K := by
  classical
  haveI : CompactSpace (K : Set ℂ) := isCompact_iff_compactSpace.mp hK
  -- The continuous restrictions as bounded continuous functions `↥K →ᵇ ℂ`.
  let cm : ℕ → C((K : Set ℂ), ℂ) := fun n =>
    ⟨(K : Set ℂ).restrict (F n), ((hF n).mono hKU).restrict⟩
  let f : ℕ → ((K : Set ℂ) →ᵇ ℂ) := fun n => mkOfCompact (cm n)
  -- Pointwise values land in the compact ball `closedBall 0 M`.
  have hin : ∀ (g : (K : Set ℂ) →ᵇ ℂ) (x : (K : Set ℂ)),
      g ∈ Set.range f → g x ∈ closedBall (0 : ℂ) M := by
    rintro _ x ⟨n, rfl⟩
    simp only [f, mkOfCompact_apply, cm, ContinuousMap.coe_mk, Set.restrict_apply,
      mem_closedBall, dist_zero_right]
    exact hbdd n x x.2
  -- Equicontinuity of the family on the compact subtype `↥K`.
  have hequiA : Equicontinuous ((↑) : Set.range f → ↥K → ℂ) := by
    intro x₀ V hV
    have hx₀U : (x₀ : ℂ) ∈ U := hKU x₀.2
    have h := hequi (x₀ : ℂ) hx₀U V hV
    have hcont : Tendsto (Subtype.val : ↥K → ℂ) (𝓝 x₀) (𝓝 (x₀ : ℂ)) :=
      continuous_subtype_val.continuousAt
    filter_upwards [hcont.eventually h] with x hx
    rintro ⟨_, n, rfl⟩
    exact hx n
  -- Arzelà–Ascoli: the closed family is compact.
  have hcomp : IsCompact (closure (Set.range f)) :=
    BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall (0 : ℂ) M)
      (Set.range f) hin hequiA
  -- Extract a convergent subsequence in `↥K →ᵇ ℂ`.
  obtain ⟨a, -, φ, hφ, htend⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  -- Extend the limit to all of `ℂ`.
  refine ⟨φ, hφ, Function.extend (Subtype.val : ↥K → ℂ) (⇑a) (fun _ => 0), ?_⟩
  have hgeq : (Function.extend (Subtype.val : ↥K → ℂ) (⇑a) (fun _ => 0)) ∘
      (Subtype.val : ↥K → ℂ) = ⇑a := by
    funext x
    exact Subtype.coe_injective.extend_apply (⇑a) (fun _ => 0) x
  -- Uniform convergence in `↥K →ᵇ ℂ` is uniform convergence on `↥K`.
  have hU1 : TendstoUniformly (fun k => ⇑(f (φ k))) (⇑a) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htend
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, hgeq]
  exact hU1

end FunctionTheory
end IsingModel
