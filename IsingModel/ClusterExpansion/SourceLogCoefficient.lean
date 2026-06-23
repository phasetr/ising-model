import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Two-point ratio as the `s²`-coefficient of the source log (GJ §18.4–18.7)

Second brick of the source-derivative cluster-expansion route to the volume-uniform two-point bound
`hbdd` (Issue #4230, item D of #4214).  The two-point generating function at a two-point source
collapses to the quadratic `Q_∅ + Q_{i,j}·s²` (`sourceGenerating_twoPoint_eq`, brick 1); the
two-point ratio `Q_{i,j}/Q_∅` is its `s²`-coefficient ratio.  To feed the *connected* cluster
expansion (which makes the bound volume-uniform via endpoint anchoring), one needs this ratio as the
`s²`-coefficient of the **logarithm** of the (normalized) generating function.

To avoid Mathlib's principal `Complex.log` (whose branch cut would obstruct differentiability when
`Q_∅` lies on the negative real axis), the logarithm is carried abstractly as a function `L`
supplied later by the source-marked Mayer expansion, satisfying
`exp(L s) = (Q_∅ + Q_{i,j} s²)/Q_∅` near `s = 0` with `L 0 = 0` and `L'(0) = 0` (no linear term, by
the handshake parity).  Then
`L''(0)/2 = Q_{i,j}/Q_∅` — the desired coefficient identity.

## Main results
* `twoPointRatio_eq_half_secondDeriv_normalizedQuad` — `½·∂²_s ((Q_∅+Q_{i,j}s²)/Q_∅)|_0 =
  Q_{i,j}/Q_∅`.
* `twoPointRatio_eq_half_secondDeriv_sourceLog` — `L''(0)/2 = Q_{i,j}/Q_∅` from the `exp(L) =` quad.

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), §18.4–18.7.
-/

namespace IsingModel

open Complex

/-- **Second derivative of the normalized quadratic** `(Q0 + Qp·s²)/Q0 = 1 + (Qp/Q0)·s²`: its
second `s`-derivative at `0` is `2·(Qp/Q0)`, so half of it is `Qp/Q0`. -/
theorem twoPointRatio_eq_half_secondDeriv_normalizedQuad (Q0 Qp : ℂ) (hQ0 : Q0 ≠ 0) :
    deriv (deriv (fun s : ℂ => (Q0 + Qp * s ^ 2) / Q0)) 0 / 2 = Qp / Q0 := by
  set c : ℂ := Qp / Q0 with hc
  have hnorm : (fun s : ℂ => (Q0 + Qp * s ^ 2) / Q0) = fun s : ℂ => 1 + c * s ^ 2 := by
    funext s; rw [hc]; field_simp [hQ0]
  rw [hnorm]
  have h1 : deriv (fun s : ℂ => 1 + c * s ^ 2) = fun s : ℂ => c * ((2 : ℂ) * s) := by
    funext s; simp
  rw [h1]
  have h2 : deriv (fun s : ℂ => c * ((2 : ℂ) * s)) = fun _ : ℂ => c * 2 := by
    funext s
    simpa using (((hasDerivAt_id' (x := s)).const_mul (2 : ℂ)).const_mul c).deriv
  rw [h2]
  field_simp

/-- **Two-point ratio as the `s²`-coefficient of the source log** (GJ §18.4–18.7): if `L` carries
the logarithm of the normalized two-point generating function near `0` — `exp(L s) =
(Q_∅ + Q_{i,j} s²)/Q_∅` eventually, with `L 0 = 0` and a vanishing first derivative `L'(0) = 0` (the
handshake parity: no linear term) and second derivative `L''(0) = D` — then `D/2 = Q_{i,j}/Q_∅`.

This carries the logarithm abstractly (it is supplied by the source-marked Mayer expansion later),
avoiding the branch cut of the principal `Complex.log`. -/
theorem twoPointRatio_eq_half_secondDeriv_sourceLog
    {L : ℂ → ℂ} {D Q0 Qp : ℂ} (hQ0 : Q0 ≠ 0)
    (hExp : ∀ᶠ s in nhds (0 : ℂ), Complex.exp (L s) = (Q0 + Qp * s ^ 2) / Q0)
    (hL0 : L 0 = 0) (hL1 : HasDerivAt L 0 0) (hL2 : HasDerivAt (deriv L) D 0)
    (hLdiff : ∀ᶠ s in nhds (0 : ℂ), DifferentiableAt ℂ L s) :
    D / 2 = Qp / Q0 := by
  set g : ℂ → ℂ := fun s => Complex.exp (L s) with hg
  set f : ℂ → ℂ := fun s => (Q0 + Qp * s ^ 2) / Q0 with hf
  -- near `0`, `g' s = exp (L s) · L' s`
  have hgderiv : deriv g =ᶠ[nhds (0 : ℂ)] fun s : ℂ => Complex.exp (L s) * deriv L s := by
    filter_upwards [hLdiff] with s hs
    simpa [hg] using deriv_cexp hs
  -- second derivative of `g` at `0`
  have hsecond : deriv (deriv g) 0 = D := by
    rw [hgderiv.deriv_eq]
    have hu : HasDerivAt (fun s : ℂ => Complex.exp (L s)) (Complex.exp (L 0) * 0) 0 := hL1.cexp
    have hprod : HasDerivAt (fun s : ℂ => Complex.exp (L s) * deriv L s)
        ((Complex.exp (L 0) * 0) * deriv L 0 + Complex.exp (L 0) * D) 0 := hu.mul hL2
    simpa [hL0] using hprod.deriv
  -- transfer through `exp (L s) = (Q0 + Qp s²)/Q0`
  have hExpEq : g =ᶠ[nhds (0 : ℂ)] f := hExp
  have hgeq : deriv (deriv g) 0 = deriv (deriv f) 0 := hExpEq.deriv.deriv_eq
  calc D / 2 = deriv (deriv g) 0 / 2 := by rw [hsecond]
    _ = deriv (deriv f) 0 / 2 := by rw [hgeq]
    _ = Qp / Q0 := by rw [hf]; exact twoPointRatio_eq_half_secondDeriv_normalizedQuad Q0 Qp hQ0

end IsingModel
