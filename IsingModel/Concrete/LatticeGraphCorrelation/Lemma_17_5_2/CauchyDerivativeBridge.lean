import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Cauchy-estimate derivative bridge from a complex extension (Issue #3026)

Real-variable derivative bounds for the GJ §17.5 Lemma 17.5.2 β-derivative increment
via Cauchy's estimate on a complex-analytic extension.

If a real function `g : ℝ → ℝ` is the real part of a complex-analytic extension
`G : ℂ → ℂ` on a disc `ball β R`, continuous up to the boundary, with `‖G‖ ≤ C` on
the boundary circle, then by Cauchy's estimate the real derivative is bounded:
`|deriv g β| ≤ C / R`.

This is the analytic device of the **Cauchy-estimate route** to the capstone
`hincr`: the β-derivative increment `dist(∂_β c_k, ∂_β c_{k+1})` equals
`|∂_β (c_k − c_{k+1})|`, and the value increment `c_k − c_{k+1}` extends
complex-analytically with a `poly·geometric` bound on a β-neighborhood, so its
derivative inherits the same `poly·geometric` bound. This converts the (already
established) *value*-increment estimate into the required *derivative*-increment
estimate without a direct higher-order covariance analysis.

References:

* Glimm–Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp. 311–312.
* Mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy's estimate),
  `HasDerivAt.real_of_complex` (real part of a complex derivative).
-/

namespace IsingModel
namespace Ambient

open Complex Metric

/-- **Cauchy-estimate bound on a real derivative via a complex extension** (Issue
#3026). If `g : ℝ → ℝ` is the real part of `G : ℂ → ℂ` on the reals
(`(G x).re = g x`), and `G` is complex-differentiable on `ball β R` and continuous
on its closure with `‖G‖ ≤ C` on the boundary circle `sphere β R`, then
`|deriv g β| ≤ C / R`.

The complex derivative `deriv G ↑β` exists (differentiability at the center), its
real part is `deriv g β` (`HasDerivAt.real_of_complex`), and `|(deriv G ↑β).re| ≤
‖deriv G ↑β‖ ≤ C / R` by `Complex.abs_re_le_norm` and Cauchy's estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. -/
theorem abs_deriv_le_of_complex_extension {g : ℝ → ℝ} {G : ℂ → ℂ} {β R C : ℝ}
    (hR : 0 < R) (hext : ∀ x : ℝ, (G x).re = g x)
    (hd : DiffContOnCl ℂ G (ball (β : ℂ) R))
    (hC : ∀ z ∈ sphere (β : ℂ) R, ‖G z‖ ≤ C) :
    |deriv g β| ≤ C / R := by
  have hGd : HasDerivAt G (deriv G (β : ℂ)) (β : ℂ) :=
    (hd.differentiableAt isOpen_ball (mem_ball_self hR)).hasDerivAt
  have hg : HasDerivAt (fun x : ℝ => (G x).re) (deriv G (β : ℂ)).re β :=
    hGd.real_of_complex
  have hgeq : (fun x : ℝ => (G (x : ℂ)).re) = g := funext hext
  rw [hgeq] at hg
  have hcauchy : ‖deriv G (β : ℂ)‖ ≤ C / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
  calc |deriv g β| = |(deriv G (β : ℂ)).re| := by rw [hg.deriv]
    _ ≤ ‖deriv G (β : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ C / R := hcauchy

/-- **Cauchy-estimate bound on a derivative difference via a complex extension**
(Issue #3026). The capstone-shaped form: if `f, h : ℝ → ℝ` are differentiable at
`β`, their difference `f − h` is the real part of a complex extension `G` analytic
on `ball β R`, continuous on the closure with `‖G‖ ≤ C` on `sphere β R`, then
`dist (deriv f β) (deriv h β) ≤ C / R`.

Since `dist (deriv f β) (deriv h β) = |deriv f β − deriv h β| = |deriv (f − h) β|`
(`deriv_sub`), this is `abs_deriv_le_of_complex_extension` applied to `g = f − h`. -/
theorem dist_deriv_le_of_complex_extension {f h : ℝ → ℝ} {G : ℂ → ℂ} {β R C : ℝ}
    (hR : 0 < R) (hf : DifferentiableAt ℝ f β) (hh : DifferentiableAt ℝ h β)
    (hext : ∀ x : ℝ, (G x).re = f x - h x)
    (hd : DiffContOnCl ℂ G (ball (β : ℂ) R))
    (hC : ∀ z ∈ sphere (β : ℂ) R, ‖G z‖ ≤ C) :
    dist (deriv f β) (deriv h β) ≤ C / R := by
  have hsub : deriv (fun x => f x - h x) β = deriv f β - deriv h β := deriv_sub hf hh
  have hkey : |deriv (fun x => f x - h x) β| ≤ C / R :=
    abs_deriv_le_of_complex_extension hR hext hd hC
  rw [Real.dist_eq, ← hsub]
  exact hkey

end Ambient
end IsingModel
