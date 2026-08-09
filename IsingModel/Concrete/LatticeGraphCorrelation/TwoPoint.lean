import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVaddTruncatedTranslation
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationSiteIndep
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

/-!
# ℤ^d correlations as functions of the separations from the origin

Defines, at `IsingModel.latticeGraph d` along `Ambient.cubicExhaustion d`, the two-point
function and the truncated two-, three- and four-point functions as the corresponding
infinite-volume correlations anchored at the origin, and records how they relate back to
the unanchored correlations.

Each definition unfolds to its anchored form by definition, without a hypothesis. Under
`Ferromagnetic` each is also computed by any other `Ambient.Exhaustion` of `Fin d → ℤ` in
place of the cubic one. Under the same condition the two-point and truncated two-point
functions recover the unanchored correlations: the infinite-volume correlation of a pair of
sites is the two-point function at their difference, and the truncated two-point
correlation of a pair is the truncated two-point function at their difference. Both of
those are proved by translating the pair so that its first site becomes the origin.

Anchoring uses the `Finset` literal `{0, r}`, and at `r = 0` that literal collapses to the
singleton `{0}`, so the two-point function at zero separation is the infinite-volume
magnetization rather than `1`. Readers taking these as physical correlations should keep to
a nonzero separation. No instance argument is taken anywhere in this module.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Two-point function on ℤ^d** (Finset-based):
`twoPointFunction d p r := correlationInfinite (latticeGraph d)
(cubicExhaustion d) p {0, r}`.

**Caveat (Finset vs physics).** Under ferromagnetic parameters and
for `r ≠ 0`, this equals the physical two-point correlation
`⟨σ_0 σ_r⟩_∞` and depends only on the separation `r`. At `r = 0`,
however, the `Finset` literal `{0, 0}` collapses to `{0}`, so
`twoPointFunction d p 0 = correlationInfinite ... {0}
= magnetizationInfinite ... 0`, *not* the physical `⟨σ_0^2⟩_∞ = 1`.
This is the same `Finset` caveat that already appears in
`susceptibility_J_zero` (`PhaseTransition.lean`). Consumers interpreting
this as the "physical" two-point function should restrict to `r ≠ 0`. -/
noncomputable def twoPointFunction (d : ℕ) (p : IsingParams ℝ)
    (r : Fin d → ℤ) : ℝ :=
  correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **Unfolding of `twoPointFunction`**: `= correlationInfinite ... {0, r}`. -/
theorem twoPointFunction_apply (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r} := rfl

/-- **`twoPointFunction` equals `correlationInfinite` under any Exhaustion**
(ferromagnetic): `twoPointFunction d p r = correlationInfinite (latticeGraph d) Λ' p {0, r}`. -/
theorem twoPointFunction_eq_correlationInfinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    twoPointFunction d p r
      = correlationInfinite (IsingModel.latticeGraph d) Λ' p {(0 : Fin d → ℤ), r} := by
  rw [twoPointFunction_apply]
  exact correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf _

/-- **Pair correlation equals `twoPointFunction` at the separation**:
for ferromagnetic `p` and any `i, j : Fin d → ℤ`,

`correlationInfinite (latticeGraph d) (cubicExhaustion d) p {i, j}
  = twoPointFunction d p (j - i)`.

Proof: translate the pair `{i, j}` by `-i` using
`correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`;
`vaddFinset (-i) {i, j} = {-i + i, -i + j} = {0, j - i}`. -/
theorem correlationInfinite_latticeGraph_pair_eq_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p {i, j}
      = twoPointFunction d p (j - i) := by
  unfold twoPointFunction
  -- Apply translation by `-i`: `{i, j}` becomes `{0, j - i}`.
  have h_translate := correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset
    d (-i) p hf {i, j}
  -- `vaddFinset (-i) {i, j} = {-i + i, -i + j} = {0, j - i}`.
  have h_finset : vaddFinset (-i) ({i, j} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), j - i} := by
    rw [vaddFinset_pair]
    have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by
      change -i + i = 0; abel
    have h2 : (-i) +ᵥ j = j - i := by
      change -i + j = j - i; abel
    rw [h1, h2]
  rw [h_finset] at h_translate
  -- Now `h_translate : correlationInfinite ... {0, j - i} = correlationInfinite ... {i, j}`.
  exact h_translate.symm

/-- **Truncated two-point function on ℤ^d**:
`truncated2TwoPoint d p r := truncated2Infinite ... p 0 r`.

Packages the site-independence / separation-dependence of the ∞-vol
truncated 2-point correlation on the translation-invariant ℤ^d
Ising model. -/
noncomputable def truncated2TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r : Fin d → ℤ) : ℝ :=
  truncated2Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r

/-- **Unfolding of `truncated2TwoPoint`**: `= truncated2Infinite ... 0 r`. -/
theorem truncated2TwoPoint_apply (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r := rfl

/-- **`truncated2TwoPoint` equals `truncated2Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated2TwoPoint_eq_truncated2Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = truncated2Infinite (IsingModel.latticeGraph d) Λ' p 0 r := by
  rw [truncated2TwoPoint_apply]
  exact truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r

/-- **Truncated 2-point correlation depends only on the separation**:
for ferromagnetic `p` and any `i, j : Fin d → ℤ`,

`truncated2Infinite ... p i j = truncated2TwoPoint d p (j - i)`.

Proof: apply `truncated2Infinite_latticeGraph_cubicExhaustion_translation`
with `t := -i`, giving `truncated2Infinite ... (-i + i) (-i + j)
= truncated2Infinite ... i j`. Simplify `-i + i = 0`, `-i + j = j - i`. -/
theorem truncated2Infinite_latticeGraph_cubicExhaustion_eq_twoPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j
      = truncated2TwoPoint d p (j - i) := by
  have h := truncated2Infinite_latticeGraph_cubicExhaustion_translation
    d (-i) p hf i j
  -- `h : truncated2Infinite ... ((-i) +ᵥ i) ((-i) +ᵥ j) = truncated2Infinite ... i j`.
  have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by change -i + i = 0; abel
  have h2 : (-i) +ᵥ j = j - i := by change -i + j = j - i; abel
  rw [h1, h2] at h
  exact h.symm

/-- **Truncated three-point (Ursell) function on ℤ^d**:
`truncated3TwoPoint d p r s := truncated3Infinite ... p 0 r s`.

Packages the translation invariance of the ∞-volume truncated 3-point
correlation: `truncated3Infinite ... p i j k` depends only on the
two differences `(j - i, k - i)`. -/
noncomputable def truncated3TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r s : Fin d → ℤ) : ℝ :=
  truncated3Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r s

/-- **Unfolding of `truncated3TwoPoint`**: `= truncated3Infinite ... 0 r s`. -/
theorem truncated3TwoPoint_apply (d : ℕ) (p : IsingParams ℝ)
    (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s
      = truncated3Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r s := rfl

/-- **`truncated3TwoPoint` equals `truncated3Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated3TwoPoint_eq_truncated3Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s
      = truncated3Infinite (IsingModel.latticeGraph d) Λ' p 0 r s := by
  rw [truncated3TwoPoint_apply]
  exact truncated3Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r s

/-- **Lebowitz truncated four-point function on ℤ^d**:
`truncated4TwoPoint d p r s u := truncated4Infinite ... p 0 r s u`.

Packages the translation invariance of the ∞-volume truncated 4-point
correlation: `truncated4Infinite ... p i j k l` depends only on the
three differences `(j - i, k - i, l - i)`. -/
noncomputable def truncated4TwoPoint (d : ℕ) (p : IsingParams ℝ)
    (r s u : Fin d → ℤ) : ℝ :=
  truncated4Infinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r s u

/-- **Unfolding of `truncated4TwoPoint`**: `= truncated4Infinite ... 0 r s u`. -/
theorem truncated4TwoPoint_apply (d : ℕ) (p : IsingParams ℝ)
    (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u
      = truncated4Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r s u := rfl

/-- **`truncated4TwoPoint` equals `truncated4Infinite` under any Exhaustion**
(ferromagnetic). -/
theorem truncated4TwoPoint_eq_truncated4Infinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u
      = truncated4Infinite (IsingModel.latticeGraph d) Λ' p 0 r s u := by
  rw [truncated4TwoPoint_apply]
  exact truncated4Infinite_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' p hf 0 r s u

end Ambient
end IsingModel
