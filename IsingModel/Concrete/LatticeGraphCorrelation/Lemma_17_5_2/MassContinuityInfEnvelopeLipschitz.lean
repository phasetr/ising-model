import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# GJ §17.5 Theorem 17.5.1 — PR-A: Lipschitz of a lower envelope via pointwise binding derivatives

A pure real-analysis fencing lemma supporting the GJ §17.5 mass-continuity argument (p.~312).  GJ
differentiates the system pseudo-mass `m⁻(σ) = inf over pairs of per-pair masses` directly: at each
`σ` the infimum is *pinned* to some binding pair whose pseudo-mass has a derivative bounded by a
constant uniform in `σ` and the pair, and this pointwise control of the binding derivative forces
the envelope `m⁻(σ)` itself to be Lipschitz — even though an infimum is generally not
differentiable.

This file isolates that real-analysis step in full generality: if a continuous function `g` on a
closed interval lies below a family `f i`, and at every interior point `g` is *equal* to some `f i`
that is differentiable there with derivative `≤ M` (one-sided form) resp. `|derivative| ≤ M` (the
two-sided absolute form), then `g` satisfies the corresponding Lipschitz increment bound.

The engine is Mathlib's Dini-type fencing theorem
`image_le_of_liminf_slope_right_le_deriv_boundary`: the binding equality `g x = f i x` plus the
domination `g ≤ f i` makes the right-slope of `g` at `x` bounded by the right-slope of `f i`, which
tends to `deriv (f i) x ≤ M`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel
namespace Ambient

open Filter Topology Set

/-- **One-sided envelope fencing** (GJ p.312 engine): if `g` is continuous on `Icc a b`, lies below
each `f i` there, and at every `x ∈ Icc a b` equals some `f i` differentiable at `x` with derivative
`≤ M`, then `g x ≤ g a + M·(x − a)` on `Icc a b`.

Applies `image_le_of_liminf_slope_right_le_deriv_boundary` with the affine boundary
`B x = g a + M·(x − a)` (`B' = M`): at `x` the binding pair `f i` (`g x = f i x`, `g z ≤ f i z`)
makes the right-slope of `g` dominated by that of `f i`, which tends to `deriv (f i) x ≤ M < r`. -/
theorem le_add_mul_sub_of_isInf_binding_deriv {ι : Type*} {a b M : ℝ}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (hle : ∀ (i : ι), ∀ x ∈ Set.Icc a b, g x ≤ f i x)
    (hbind : ∀ x ∈ Set.Icc a b, ∃ i : ι, g x = f i x ∧
      ∃ dv : ℝ, HasDerivAt (f i) dv x ∧ dv ≤ M) :
    ∀ x ∈ Set.Icc a b, g x ≤ g a + M * (x - a) := by
  set B : ℝ → ℝ := fun x => g a + M * (x - a) with hB_def
  have hBderiv : ∀ x : ℝ, HasDerivAt B M x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => M * (x - a)) M x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul M
    simpa [hB_def] using h1.const_add (g a)
  have hBcont : ContinuousOn B (Set.Icc a b) :=
    fun x _ => (hBderiv x).continuousAt.continuousWithinAt
  have hB' : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B M (Set.Ici x) x :=
    fun x _ => (hBderiv x).hasDerivWithinAt
  have ha0 : g a ≤ B a := by simp [hB_def]
  -- the slope-frequency bound at each interior point, from the binding pair.
  have bound : ∀ x ∈ Set.Ico a b, ∀ r, M < r → ∃ᶠ z in 𝓝[>] x, slope g x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    obtain ⟨i, hgi, dv, hderiv, hdvM⟩ := hbind x hxIcc
    have hdvr : dv < r := lt_of_le_of_lt hdvM hr
    -- slope of `f i` at `x` tends to `dv`, hence is eventually `< r` to the right.
    have hslope : Tendsto (slope (f i) x) (𝓝[≠] x) (𝓝 dv) :=
      hasDerivAt_iff_tendsto_slope.mp hderiv
    have hevNe : ∀ᶠ z in 𝓝[≠] x, slope (f i) x z < r := hslope.eventually_lt_const hdvr
    have hevGt : ∀ᶠ z in 𝓝[>] x, slope (f i) x z < r :=
      hevNe.filter_mono (nhdsWithin_mono x (fun z hz => ne_of_gt hz))
    -- eventually to the right, `z < b` so `z ∈ Icc a b`, giving the domination.
    have hevlt : ∀ᶠ z in 𝓝[>] x, z < b := by
      have : ∀ᶠ z in 𝓝 x, z < b := eventually_lt_nhds hx.2
      exact this.filter_mono nhdsWithin_le_nhds
    have hevGtSelf : ∀ᶠ z in 𝓝[>] x, x < z := eventually_mem_nhdsWithin.mono (fun z hz => hz)
    -- combine: eventually `slope g x z < r`.
    have : ∀ᶠ z in 𝓝[>] x, slope g x z < r := by
      filter_upwards [hevGt, hevlt, hevGtSelf] with z hzr hzb hzx
      have hzIcc : z ∈ Set.Icc a b := ⟨le_of_lt (lt_of_le_of_lt hx.1 hzx), hzb.le⟩
      have hzpos : 0 < z - x := by linarith
      have hnnum : g z - g x ≤ f i z - f i x := by
        have := hle i z hzIcc
        rw [hgi]; linarith
      have hslopele : slope g x z ≤ slope (f i) x z := by
        rw [slope_def_field, slope_def_field]
        exact (div_le_div_iff_of_pos_right hzpos).mpr hnnum
      exact lt_of_le_of_lt hslopele hzr
    exact this.frequently
  exact fun x hx => image_le_of_liminf_slope_right_le_deriv_boundary hg ha0 hBcont hB' bound hx

/-- **Two-sided envelope Lipschitz** (GJ p.312): under the same hypotheses with `|deriv| ≤ M`,
the envelope `g` satisfies `|g b − g a| ≤ M·(b − a)` on `[a, b]` (for `a ≤ b`).

Forward `g b − g a ≤ M(b−a)` is `le_add_mul_sub_of_isInf_binding_deriv` at `x = b`.  Backward
`g a − g b ≤ M(b−a)` reflects via `t ↦ a + b − t`: the reflected family `F i t := f i (a+b−t)` has
derivative `−dv` (`|−dv| ≤ M`) and the same binding/domination, so the forward lemma applied to the
reflection yields `g a ≤ g b + M(b−a)`. -/
theorem abs_sub_le_of_isInf_binding_deriv {ι : Type*} {a b M : ℝ}
    (hab : a ≤ b)
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (hle : ∀ (i : ι), ∀ x ∈ Set.Icc a b, g x ≤ f i x)
    (hbind : ∀ x ∈ Set.Icc a b, ∃ i : ι, g x = f i x ∧
      ∃ dv : ℝ, HasDerivAt (f i) dv x ∧ |dv| ≤ M) :
    |g b - g a| ≤ M * (b - a) := by
  -- forward direction: `g b ≤ g a + M(b - a)`.
  have hbindFwd : ∀ x ∈ Set.Icc a b, ∃ i : ι, g x = f i x ∧
      ∃ dv : ℝ, HasDerivAt (f i) dv x ∧ dv ≤ M := by
    intro x hx
    obtain ⟨i, hgi, dv, hderiv, hdvM⟩ := hbind x hx
    exact ⟨i, hgi, dv, hderiv, le_trans (le_abs_self dv) hdvM⟩
  have hfwd : g b ≤ g a + M * (b - a) :=
    le_add_mul_sub_of_isInf_binding_deriv hg hle hbindFwd b ⟨hab, le_refl b⟩
  -- reflected setup: `G t = g (a + b - t)`, `F i t = f i (a + b - t)`.
  set φ : ℝ → ℝ := fun t => a + b - t with hφ_def
  have hφ_maps : ∀ t ∈ Set.Icc a b, φ t ∈ Set.Icc a b := by
    intro t ht; constructor <;> simp only [hφ_def] <;> [linarith [ht.2]; linarith [ht.1]]
  have hφderiv : ∀ t : ℝ, HasDerivAt φ (-1) t := by
    intro t
    simpa [hφ_def] using (hasDerivAt_const t (a + b)).sub (hasDerivAt_id t)
  set G : ℝ → ℝ := fun t => g (φ t) with hG_def
  set F : ι → ℝ → ℝ := fun i t => f i (φ t) with hF_def
  have hGcont : ContinuousOn G (Set.Icc a b) := by
    refine hg.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro t ht; exact hφ_maps t ht
  have hGle : ∀ (i : ι), ∀ t ∈ Set.Icc a b, G t ≤ F i t :=
    fun i t ht => hle i (φ t) (hφ_maps t ht)
  have hGbind : ∀ t ∈ Set.Icc a b, ∃ i : ι, G t = F i t ∧
      ∃ dv : ℝ, HasDerivAt (F i) dv t ∧ dv ≤ M := by
    intro t ht
    obtain ⟨i, hgi, dv, hderiv, hdvM⟩ := hbind (φ t) (hφ_maps t ht)
    refine ⟨i, by simp [hG_def, hF_def, hgi], -dv, ?_, ?_⟩
    · have : HasDerivAt (fun t => f i (φ t)) (dv * (-1)) t := hderiv.comp t (hφderiv t)
      simpa [hF_def, mul_neg, mul_one] using this
    · have := neg_le_neg (neg_abs_le dv)
      simp only [neg_neg] at this
      exact le_trans this hdvM
  have hbwd : G b ≤ G a + M * (b - a) :=
    le_add_mul_sub_of_isInf_binding_deriv hGcont hGle hGbind b ⟨hab, le_refl b⟩
  have hGa : G a = g b := by simp [hG_def, hφ_def]
  have hGb : G b = g a := by simp [hG_def, hφ_def]
  rw [hGa, hGb] at hbwd
  rw [abs_le]
  constructor <;> linarith

end Ambient
end IsingModel
