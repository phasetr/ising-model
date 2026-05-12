/- TwoPoint.lean
Two-point, truncated two-point, three-point, four-point functions on ℤ^d,
together with their free-energy and correlation monotonicity wrappers.
All definitions and theorems are concrete specialisations of the abstract
`IsingModel.Ambient.*` results to `(IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Two-point function on ℤ^d -/

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

/-- **Symmetry of the two-point function under sign inversion**:
`twoPointFunction d p r = twoPointFunction d p (-r)`.

Proof: `{0, r} = {r, 0}` (unordered pair); translating by `-r` gives
`{-r, 0} = {0, -r}`, and the correlation is invariant under translation. -/
theorem twoPointFunction_symm
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    twoPointFunction d p r = twoPointFunction d p (-r) := by
  -- `{0, r} = {r, 0}` (unordered).
  have h_pair : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ))
      = {r, (0 : Fin d → ℤ)} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_zero_sub : (0 : Fin d → ℤ) - r = -r := by abel
  -- Chain:
  -- `twoPointFunction d p r = correlationInfinite ... {0, r}`
  -- `= correlationInfinite ... {r, 0}` (by h_pair)
  -- `= twoPointFunction d p (0 - r)` (by the pair-to-twoPoint identity)
  -- `= twoPointFunction d p (-r)` (by h_zero_sub).
  calc twoPointFunction d p r
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r} := rfl
    _ = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p {r, (0 : Fin d → ℤ)} := by rw [h_pair]
    _ = twoPointFunction d p ((0 : Fin d → ℤ) - r) :=
          correlationInfinite_latticeGraph_pair_eq_twoPointFunction d p hf r 0
    _ = twoPointFunction d p (-r) := by rw [h_zero_sub]

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

/-- **Symmetry of the truncated two-point function**:
`truncated2TwoPoint d p r = truncated2TwoPoint d p (-r)`.

Proof: `truncated2Infinite_symm` swaps the two site arguments;
`truncated2Infinite ... 0 r = truncated2Infinite ... r 0`, which by
`_eq_twoPoint` equals `truncated2TwoPoint d p (0 - r) = truncated2TwoPoint
d p (-r)`. -/
theorem truncated2TwoPoint_symm
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r = truncated2TwoPoint d p (-r) := by
  have h_symm := truncated2Infinite_symm (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0 r
  -- h_symm : truncated2Infinite ... 0 r = truncated2Infinite ... r 0
  have h_zero_sub : (0 : Fin d → ℤ) - r = -r := by abel
  calc truncated2TwoPoint d p r
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 r := rfl
    _ = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p r 0 := h_symm
    _ = truncated2TwoPoint d p ((0 : Fin d → ℤ) - r) :=
          truncated2Infinite_latticeGraph_cubicExhaustion_eq_twoPoint d p hf r 0
    _ = truncated2TwoPoint d p (-r) := by rw [h_zero_sub]

/-! ## r = 0 collapse of the ℤ^d two-point quantities -/

/-- **`twoPointFunction` at `r = 0` collapses to the magnetization**:
`twoPointFunction d p 0 = magnetizationInfinite (latticeGraph d)
(cubicExhaustion d) p 0`.

This is the Finset-vs-physics caveat highlighted in the
`twoPointFunction` doc comment: the Finset literal `{0, 0}` collapses
to the singleton `{0}`, so the "two-point function at zero separation"
equals the magnetization, *not* the physical `⟨σ_0^2⟩ = 1`. -/
@[simp]
theorem twoPointFunction_zero (d : ℕ) (p : IsingParams ℝ) :
    twoPointFunction d p 0
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 := by
  unfold twoPointFunction magnetizationInfinite
  -- `{0, 0} = {0}` in Finset (duplicate collapse via insert_self).
  have : ({(0 : Fin d → ℤ), (0 : Fin d → ℤ)} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ)} := by
    simp
  rw [this]

/-- **`truncated2TwoPoint` at `r = 0`**: equals `M · (1 − M)` where `M` is
the site-independent magnetization at `0`.

Unfolds `truncated2TwoPoint d p 0 = truncated2Infinite ... p 0 0
= correlationInfinite ... {0, 0} − correlationInfinite ... {0} · correlationInfinite ... {0}
= M − M² = M(1 − M)`. -/
theorem truncated2TwoPoint_zero
    (d : ℕ) (p : IsingParams ℝ) :
    truncated2TwoPoint d p 0
      = (magnetizationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) p 0)
        * (1 - magnetizationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) p 0) := by
  unfold truncated2TwoPoint truncated2Infinite magnetizationInfinite
  -- `correlationInfinite ... {0, 0} = correlationInfinite ... {0}` by Finset collapse.
  have h_collapse : ({(0 : Fin d → ℤ), (0 : Fin d → ℤ)} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ)} := by simp
  rw [h_collapse]
  ring

/-! ## Three-point function on ℤ^d -/

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

/-- **ℤ^d `truncated3Infinite` swap symmetries**. -/
theorem truncated3Infinite_latticeGraph_swap_ij
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p j i k :=
  truncated3Infinite_swap_ij (IsingModel.latticeGraph d) Λ p i j k

theorem truncated3Infinite_latticeGraph_swap_jk
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p i k j :=
  truncated3Infinite_swap_jk (IsingModel.latticeGraph d) Λ p i j k

theorem truncated3Infinite_latticeGraph_swap_ik
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p k j i :=
  truncated3Infinite_swap_ik (IsingModel.latticeGraph d) Λ p i j k

/-- **ℤ^d `truncated4Infinite` swap symmetries** (adjacent swaps). -/
theorem truncated4Infinite_latticeGraph_swap_ij
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p j i k l :=
  truncated4Infinite_swap_ij (IsingModel.latticeGraph d) Λ p i j k l

theorem truncated4Infinite_latticeGraph_swap_jk
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i k j l :=
  truncated4Infinite_swap_jk (IsingModel.latticeGraph d) Λ p i j k l

theorem truncated4Infinite_latticeGraph_swap_kl
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i j l k :=
  truncated4Infinite_swap_kl (IsingModel.latticeGraph d) Λ p i j k l

/-- **Three-point correlation depends only on two separations**:
for ferromagnetic `p` and any `i, j, k : Fin d → ℤ`,

`truncated3Infinite ... p i j k = truncated3TwoPoint d p (j - i) (k - i)`.

Proof: apply `truncated3Infinite_latticeGraph_cubicExhaustion_translation`
with `t := -i`, giving `truncated3Infinite ... (-i + i) (-i + j) (-i + k)
= truncated3Infinite ... i j k`. Simplify `-i + i = 0`, `-i + j = j - i`,
`-i + k = k - i`. -/
theorem truncated3Infinite_latticeGraph_cubicExhaustion_eq_threePoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j k
      = truncated3TwoPoint d p (j - i) (k - i) := by
  have h := truncated3Infinite_latticeGraph_cubicExhaustion_translation
    d (-i) p hf i j k
  -- `h : truncated3Infinite ... ((-i) +ᵥ i) ((-i) +ᵥ j) ((-i) +ᵥ k)
  --      = truncated3Infinite ... i j k`.
  have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by change -i + i = 0; abel
  have h2 : (-i) +ᵥ j = j - i := by change -i + j = j - i; abel
  have h3 : (-i) +ᵥ k = k - i := by change -i + k = k - i; abel
  rw [h1, h2, h3] at h
  exact h.symm

/-! ## Four-point function on ℤ^d -/

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

/-- **Four-point correlation depends only on three separations**:
for ferromagnetic `p` and any `i, j, k, l : Fin d → ℤ`,

`truncated4Infinite ... p i j k l = truncated4TwoPoint d p (j - i) (k - i) (l - i)`.

Proof: translation by `-i`. -/
theorem truncated4Infinite_latticeGraph_cubicExhaustion_eq_fourPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j k l
      = truncated4TwoPoint d p (j - i) (k - i) (l - i) := by
  have h := truncated4Infinite_latticeGraph_cubicExhaustion_translation
    d (-i) p hf i j k l
  have h1 : (-i) +ᵥ i = (0 : Fin d → ℤ) := by change -i + i = 0; abel
  have h2 : (-i) +ᵥ j = j - i := by change -i + j = j - i; abel
  have h3 : (-i) +ᵥ k = k - i := by change -i + k = k - i; abel
  have h4 : (-i) +ᵥ l = l - i := by change -i + l = l - i; abel
  rw [h1, h2, h3, h4] at h
  exact h.symm

/-! ## Relating truncated2TwoPoint, twoPointFunction, and magnetization -/

/-- **`truncated2TwoPoint = twoPointFunction - M^2`** on ℤ^d:
for ferromagnetic `p` and any separation `r : Fin d → ℤ`,

`truncated2TwoPoint d p r = twoPointFunction d p r
  - (magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0)^2`.

Unfolding: `truncated2Infinite ... p 0 r = correlationInfinite ... {0, r}
  - magnetizationInfinite ... p 0 · magnetizationInfinite ... p r`;
site-independence gives `magnetizationInfinite ... p r
= magnetizationInfinite ... p 0`, so the last term is a square.
The `correlationInfinite ... {0, r}` factor is `twoPointFunction d p r`
by definition. -/
theorem truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = twoPointFunction d p r
        - (magnetizationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) p 0)^2 := by
  unfold truncated2TwoPoint twoPointFunction truncated2Infinite magnetizationInfinite
  -- `truncated2Infinite ... p 0 r = correlationInfinite ... {0, r}
  --   - correlationInfinite ... {0} · correlationInfinite ... {r}`.
  -- Site-independence: `correlationInfinite ... {r} = magnetizationInfinite ... r
  --   = magnetizationInfinite ... 0 = correlationInfinite ... {0}`.
  have h_site : correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p {r}
    = correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ)} := by
    change magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p r
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0
    exact magnetizationInfinite_latticeGraph_cubicExhaustion_eq d p hf r 0
  rw [h_site]
  -- Now it's `correlationInfinite ... {0, r} - correlationInfinite ... {0}^2`
  -- = `twoPointFunction d p r - magnetizationInfinite ... 0 ^ 2`.
  ring

/-- **`truncated3TwoPoint` at `h = 0` vanishes (pairwise distinct, nonzero)**:
`truncated3TwoPoint d ⟨J, 0, β⟩ r s = 0`.

Z₂ symmetry at `h = 0` forces all odd-cardinality spin products
(and hence the Ursell 3-point combination) to vanish.
Concrete specialisation of `truncated3Infinite_h_zero_of_distinct`. -/
theorem truncated3TwoPoint_h_zero_of_distinct
    (d : ℕ) (J β : ℝ)
    {r s : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hrs : r ≠ s)
    (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) r s = 0 :=
  truncated3Infinite_h_zero_of_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β
    hr hrs hs

/-- **`truncated3TwoPoint` at `J = 0` vanishes (pairwise distinct, nonzero)**:
for ferromagnetic `⟨0, h, β⟩` and `0 ≠ r, 0 ≠ s, r ≠ s`,
`truncated3TwoPoint d ⟨0, h, β⟩ r s = 0`.

Concrete ℤ^d specialisation of `truncated3Infinite_J_zero_of_pairwise_distinct`
at `i = 0, j = r, k = s`. Cluster property: at J=0 distinct sites are
independent, so the 3-point truncated function vanishes. -/
theorem truncated3TwoPoint_J_zero_of_distinct
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r s : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hrs : r ≠ s)
    (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r s = 0 :=
  truncated3Infinite_J_zero_of_pairwise_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf
    hr hrs hs

/-- **`truncated4TwoPoint` at `J = 0` closed form** (ferromagnetic,
pairwise distinct + nonzero separations):

`truncated4TwoPoint d ⟨0, h, β⟩ r s u = -2 · tanh(β · h)^4`.

Concrete ℤ^d specialisation of `truncated4Infinite_J_zero_of_pairwise_distinct`
at `i = 0, j = r, k = s, l = u`. Non-interacting Lebowitz 4-point
closed form. -/
theorem truncated4TwoPoint_J_zero_of_distinct
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    truncated4TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r s u
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_pairwise_distinct
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf
    hr hs hu hrs hru hsu

/-- **`truncated4TwoPoint` at `β = 0` vanishes**:
`truncated4TwoPoint d ⟨J, h, 0⟩ r s u = 0`.

All four Lebowitz terms vanish at β=0. -/
theorem truncated4TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r s u = 0 := by
  unfold truncated4TwoPoint truncated4Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {s, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), u} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring

/-- **`truncated3TwoPoint` at `β = 0` vanishes**:
`truncated3TwoPoint d ⟨J, h, 0⟩ r s = 0`.

All seven Ursell terms (one 3-set, three pairs, three singletons) vanish
at β=0 via `correlationInfinite_beta_zero_vanish`. Direct computation. -/
theorem truncated3TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r s = 0 := by
  unfold truncated3TwoPoint truncated3Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {s} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring

/-- **`twoPointFunction` at `J = h = 0` is 0**:
`twoPointFunction d ⟨0, 0, β⟩ r = 0`.

Both couplings vanish ⇒ the Hamiltonian is identically zero
⇒ all configurations are equiprobable ⇒ all nonempty-observable
correlations vanish. Direct from `correlationInfinite_zero_params_vanish`. -/
theorem twoPointFunction_zero_params
    (d : ℕ) (β : ℝ) (r : Fin d → ℤ) :
    twoPointFunction d (⟨0, 0, β⟩ : IsingParams ℝ) r = 0 := by
  unfold twoPointFunction
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ), r} (by simp)

/-- **`twoPointFunction` at `β = 0`**: `twoPointFunction d ⟨J, h, 0⟩ r = 0`.

At infinite temperature `β = 0`, all correlation functions vanish
(Boltzmann weight is `exp 0 = 1`, and the summand is the spin product
which sums to zero over all configurations). Concrete specialisation
of `correlationInfinite_beta_zero_vanish` at `A = {0, r}` (nonempty). -/
theorem twoPointFunction_beta_zero
    (d : ℕ) (J h : ℝ) (r : Fin d → ℤ) :
    twoPointFunction d (⟨J, h, 0⟩ : IsingParams ℝ) r = 0 := by
  unfold twoPointFunction
  exact correlationInfinite_beta_zero_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h
    {(0 : Fin d → ℤ), r} (by simp)

/-- **`twoPointFunction` at `J = 0`** (ferromagnetic `⟨0, h, β⟩`), for
distinct sites: `twoPointFunction d ⟨0, h, β⟩ r = tanh(β · h)^2`
for `r ≠ 0`.

Proof: `correlationInfinite_J_zero` gives
`correlationInfinite ... ⟨0, h, β⟩ A = tanh(β h)^|A|`; with `A = {0, r}`
and `r ≠ 0`, `|A| = 2`, giving `tanh(β h)^2`. -/
theorem twoPointFunction_J_zero_of_ne_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    twoPointFunction d (⟨0, h, β⟩ : IsingParams ℝ) r
      = Real.tanh (β * h) ^ 2 := by
  unfold twoPointFunction
  -- `correlationInfinite ... ⟨0, h, β⟩ {0, r} = tanh(β h)^|{0, r}| = tanh(β h)^2`.
  rw [correlationInfinite_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hf {(0 : Fin d → ℤ), r}]
  -- `|{0, r}| = 2` since `0 ≠ r`.
  have h_card : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair]
    exact (Ne.symm hr)
  rw [h_card]

/-! ## Moved: freeEnergy / magnetizationInfinite cubicExhaustion wrappers

The 34 ℤ^d `freeEnergyAlongExhaustion_latticeGraph` /
`freeEnergyInfinite_latticeGraph` / cubicExhaustion convergence,
trivial-slice, monotonicity, and bound wrappers (plus the two
`spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_*`
variants that proved them) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointFreeEnergy`.
The three `magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_*`
variants remain in this parent file.
The legacy import path is preserved by re-importing the new child.
-/

/-- **J-monotonicity of `spontaneousMagnetization` on ℤ^d** at any site. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ i

/-- **β-monotonicity of `spontaneousMagnetization` on ℤ^d** at any site. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ i

/-- **J-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ i

/-- **h-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ i

/-- **β-monotonicity of `magnetizationInfinite` on ℤ^d** at any site. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh i

/-! ## Moved: ambient-subgraph monotonicity + bot wrappers

The 24 ℤ^d wrappers covering ambient-subgraph monotonicity from
`⊥` to `latticeGraph d` (`inducedGraph_latticeGraph_bot`,
`*_bot_le_latticeGraph`, and
`*_latticeGraph_monotone_ambient_subgraph` for `freeEnergy*`,
`partitionFunction*`, `correlation*`, `magnetization*`,
`spontaneous*`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointAmbientBot`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: truncatedInfinite_latticeGraph wrappers

The 16 ℤ^d `truncated2Infinite_latticeGraph_*` wrappers (bounds,
nonneg, symmetry, trivial slices `J_zero` / `β_zero` / `h_zero`),
`truncated3Infinite_latticeGraph_apply`, and
`truncated4Infinite_latticeGraph_apply` now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedInfinite`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: truncated3/4Infinite_latticeGraph trivial-slice wrappers

The 18 ℤ^d `truncated3Infinite_latticeGraph_*` and
`truncated4Infinite_latticeGraph_*` trivial-slice + nonpos +
exhaustion-independence wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncatedHigher`.
The legacy import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d correlationInfinite wrappers

The 7 concrete ℤ^d `correlationInfinite_latticeGraph_*` wrappers
(`_le_one`, `_nonneg`, `_indep_exhaustion`,
`_cubicExhaustion_monotone_h`, `_beta`, `_J`, `_gks_second`) now
live in
`IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfinite`.
The legacy import path is preserved by re-importing the new child.
-/


end Ambient
end IsingModel
