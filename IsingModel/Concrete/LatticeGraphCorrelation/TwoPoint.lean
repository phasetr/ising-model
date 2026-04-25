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

/-- **ℤ^d Fekete J=0 convergence with hcard_add** (any-Exhaustion): given
BED + additive card + non-degenerate base step, `freeEnergyAlongExhaustion
⟨0, h, β⟩` converges to `freeEnergyInfinite ⟨0, h, β⟩`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero_tendsto_of_hcard_add
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_J_zero_tendsto_of_hcard_add
    (IsingModel.latticeGraph d) Λ h β hBED hcard_add hcard_one

/-- **ℤ^d Fekete β=0 convergence with hcard_add** (any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero_tendsto_of_hcard_add
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))) :=
  freeEnergyAlongExhaustion_beta_zero_tendsto_of_hcard_add
    (IsingModel.latticeGraph d) Λ J h hBED hcard_add hcard_one

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED** (any-Exhaustion):
if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`, log Z is super-additive,
and BED holds, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjoint_tower
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjoint_tower
    (IsingModel.latticeGraph d) Λ p hBED hcard_add hsuper hcard_one

/-- **ℤ^d Fekete-style convergence under disjoint-tower + BED, bundled form**
(any-Exhaustion): same as `_of_disjoint_tower` but takes a
`DisjointTowerHypotheses` record. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_disjointTowerHypotheses
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (h : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    (IsingModel.latticeGraph d) Λ p hBED h

/-- **ℤ^d Fekete-style convergence under super-additivity**
(any-Exhaustion): if `|Λ.volume (m+n)| = |Λ.volume m| + |Λ.volume n|`,
log Z is super-additive on this additive grading, the range is bounded above,
and `|Λ.volume 1| ≠ 0`, then `freeEnergyAlongExhaustion → freeEnergyInfinite`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_superadditive
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n,
        Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume m) p)
          + Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
              (Λ.volume n) p)
        ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
            (Λ.volume (m + n)) p))
    (hbdd : BddAbove (Set.range
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop
      (nhds (freeEnergyInfinite (IsingModel.latticeGraph d) Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_superadditive
    (IsingModel.latticeGraph d) Λ p hcard_add hsuper hbdd hcard_one

/-- **ℤ^d generic tendsto helper**: if the stagewise
`freeEnergyAlongExhaustion` is eventually constantly `c`, it tends to `c`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_tendsto_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n = c) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
      Filter.atTop (nhds c) :=
  freeEnergyAlongExhaustion_tendsto_of_eventually_const
    (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at J=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_J_zero_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) :=
  freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ h β hne

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at β=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_beta_zero_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) :=
  freeEnergyAlongExhaustion_beta_zero_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d freeEnergyAlongExhaustion Tendsto at J=h=0 under eventually-nonempty**
(any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_zero_params_tendsto_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto
      (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) :=
  freeEnergyAlongExhaustion_zero_params_tendsto_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d freeEnergyInfinite at β=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ J h hne

/-- **ℤ^d freeEnergyInfinite at J=h=0 under eventually-nonempty** (any-Exhaustion):
`= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ β hne

/-- **ℤ^d freeEnergyInfinite at J=0 under eventually-nonempty** (any-Exhaustion):
`= log(2·cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero_of_eventually_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_eventually_nonempty
    (IsingModel.latticeGraph d) Λ h β hne

/-- **ℤ^d freeEnergyInfinite at β = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0** (any-Exhaustion): `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d freeEnergyInfinite at J = 0** (any-Exhaustion): `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d) Λ h β

/-- **ℤ^d freeEnergyInfinite at β = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (J h : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h

/-- **ℤ^d freeEnergyInfinite at J = h = 0**: `= log 2`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) [Nonempty (Fin d → ℤ)] (β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β

/-- **ℤ^d freeEnergyInfinite at J = 0**: `= log(2 cosh(β·h))`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)] (h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_nonempty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β

/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Lower bound** `freeEnergyInfinite ≥ log 2` on ℤ^d (any Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **Sharp lower bound** `freeEnergyInfinite ≥ log(2 cosh(βh))` on ℤ^d
(any Exhaustion with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_ge_log_two_cosh
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_ge_log_two_cosh (IsingModel.latticeGraph d)
    Λ p hf (c := c) hc

/-- **ℤ^d ∞-vol free-energy sandwich bound** (ferromagnetic):
`log 2 ≤ freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p
  ≤ log 2 + |β|·(|J|·d + |h|)`.

Capstone for the ∞-vol free-energy bounds on ℤ^d. Uses BED `c = d`
(PR #246) for the upper bound, and `freeEnergyInfinite_ge_log_two`
for the lower. Note: `[Nonempty (Fin d → ℤ)]` holds for every `d` since
`Fin 0 → ℤ` has exactly one element (empty function) and `Fin d → ℤ`
with `d ≥ 1` has `fun _ => 0`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_bounds
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log 2
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
    ∧ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p
        ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  have hc : ∀ n, ((Ambient.cubicExhaustion d).volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card : ℝ)
        ≤ (d : ℝ) * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _) := by
    intro n _
    exact inducedLatticeGraph_card_edgeFinset_le d
      ((Ambient.cubicExhaustion d).volume n)
  refine ⟨?_, ?_⟩
  · exact freeEnergyInfinite_ge_log_two (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p hf hc
  · exact freeEnergyInfinite_le_uniform_upper_bound
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf hc

/-- **`|h|`-monotonicity of `freeEnergyInfinite` on ℤ^d**:
`|h₁| ≤ |h₂| ⇒ freeEnergyInfinite ⟨J, h₁, β⟩ ≤ freeEnergyInfinite ⟨J, h₂, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  refine freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_ hh
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d**:
`freeEnergyInfinite ⟨J, -h, β⟩ = freeEnergyInfinite ⟨J, h, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d J-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ hc

/-- **ℤ^d h-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ hc

/-- **ℤ^d β-monotonicity of `freeEnergyInfinite`** (any-Exhaustion with
caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh hc

/-- **ℤ^d `|h|`-monotonicity of `freeEnergyInfinite`** (any-Exhaustion
with caller-supplied BED). -/
theorem freeEnergyInfinite_latticeGraph_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _))
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d) Λ hJ hβ hc hh

/-- **J-monotonicity of `freeEnergyInfinite` on ℤ^d** under the concrete
BED constant `c = d` (PR #246). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **β-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  refine freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

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

/-- **`⊥` ≤ `latticeGraph d` freeEnergyInfinite monotonicity** on ℤ^d. -/
theorem freeEnergyInfinite_bot_le_latticeGraph
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_monotone_ambient_subgraph (G₂ := IsingModel.latticeGraph d)
    bot_le (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite ambient-subgraph monotonicity** up to
`latticeGraph d` (ferromagnetic, `cubicExhaustion`): for any
`G₁ ≤ latticeGraph d`, `freeEnergyInfinite G₁ Λ p ≤
freeEnergyInfinite (latticeGraph d) Λ p`. BED supplied by
`inducedLatticeGraph_card_edgeFinset_le`. -/
theorem freeEnergyInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {G₁ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ IsingModel.latticeGraph d)
    [∀ n, Fintype (Ambient.inducedGraph G₁
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite G₁ (Ambient.cubicExhaustion d) p
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_monotone_ambient_subgraph (G₂ := IsingModel.latticeGraph d)
    hG (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d inducedGraph of `⊥` = `⊥`** on any Λ. -/
@[simp]
theorem inducedGraph_latticeGraph_bot (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ = ⊥ :=
  Ambient.inducedGraph_bot Λ

/-- **ℤ^d freeEnergyAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem freeEnergyAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n :=
  freeEnergyAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem partitionFunctionAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d correlationAlongExhaustion ambient-subgraph monotonicity** from ⊥. -/
theorem correlationAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ))
    (n : ℕ) :
    correlationAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ))
        (Ambient.cubicExhaustion d) p A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_monotone_ambient_subgraph bot_le
    (Ambient.cubicExhaustion d) p hf A n

/-- **ℤ^d partitionFunctionΛ ambient-subgraph monotonicity** from ⊥. -/
theorem partitionFunctionΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_monotone_ambient_subgraph bot_le Λ p hf

/-- **ℤ^d freeEnergyΛ ambient-subgraph monotonicity** from ⊥. -/
theorem freeEnergyΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_monotone_ambient_subgraph bot_le Λ p hf

/-- **ℤ^d correlationΛ ambient-subgraph monotonicity** from ⊥. -/
theorem correlationΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    correlationΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p A
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_monotone_ambient_subgraph bot_le Λ p hf A

/-- **ℤ^d `log Z_Λ` ambient-subgraph `⊥ ≤ latticeGraph d`** (ferromagnetic):
from `partitionFunctionΛ_bot_le_latticeGraph` via `Real.log_le_log`. -/
theorem log_partitionFunctionΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p)
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  Real.log_le_log (partitionFunctionΛ_pos _ Λ p)
    (partitionFunctionΛ_bot_le_latticeGraph d Λ p hf)

/-- **ℤ^d freeEnergyΛ ambient-subgraph monotonicity** (ferromagnetic):
for `G₁ ≤ G₂`, `freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p`. -/
theorem freeEnergyΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ G₁ Λ p ≤ freeEnergyΛ G₂ Λ p :=
  freeEnergyΛ_monotone_ambient_subgraph hG Λ p hf

/-- **ℤ^d freeEnergyAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    freeEnergyAlongExhaustion G₁ Λ p n
      ≤ freeEnergyAlongExhaustion G₂ Λ p n :=
  freeEnergyAlongExhaustion_monotone_ambient_subgraph hG Λ p hf n

/-- **ℤ^d partitionFunctionΛ ambient-subgraph monotonicity** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G₁ Λ p ≤ partitionFunctionΛ G₂ Λ p :=
  partitionFunctionΛ_monotone_ambient_subgraph hG Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion G₁ Λ p n
      ≤ partitionFunctionAlongExhaustion G₂ Λ p n :=
  partitionFunctionAlongExhaustion_monotone_ambient_subgraph hG Λ p hf n

/-- **ℤ^d correlationΛ ambient-subgraph monotonicity** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    correlationΛ G₁ Λ p A ≤ correlationΛ G₂ Λ p A :=
  correlationΛ_monotone_ambient_subgraph hG Λ p hf A

/-- **ℤ^d correlationAlongExhaustion ambient-subgraph monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion G₁ Λ p A n
      ≤ correlationAlongExhaustion G₂ Λ p A n :=
  correlationAlongExhaustion_monotone_ambient_subgraph hG Λ p hf A n

/-- **ℤ^d correlationInfinite ambient-subgraph monotonicity**. -/
theorem correlationInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite G₁ Λ p A ≤ correlationInfinite G₂ Λ p A :=
  correlationInfinite_monotone_ambient_subgraph hG Λ p hf A

/-- **ℤ^d `log Z_{Λ_n}` ambient-subgraph `⊥ ≤ latticeGraph d`** per stage
(ferromagnetic, `cubicExhaustion`). -/
theorem log_partitionFunctionAlongExhaustion_bot_le_latticeGraph
    (d : ℕ)
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      ((Ambient.cubicExhaustion d).volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion
        (⊥ : SimpleGraph (Fin d → ℤ)) (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion
          (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n) :=
  Real.log_le_log
    (partitionFunctionAlongExhaustion_pos _ (Ambient.cubicExhaustion d) p n)
    (partitionFunctionAlongExhaustion_bot_le_latticeGraph d p hf n)

/-- **`⊥` ≤ `latticeGraph d` correlation monotonicity** on ℤ^d:
`correlationInfinite ⊥ Λ p A ≤ correlationInfinite (latticeGraph d) Λ p A`
(ferromagnetic). Any two ambient graphs with `⊥ ≤ G` give ambient-subgraph
monotonicity. Here we instantiate at `⊥ ≤ latticeGraph d`. -/
theorem correlationInfinite_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ p A
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationInfinite_monotone_ambient_subgraph bot_le Λ p hf A

/-- **`⊥` ≤ `latticeGraph d` magnetizationΛ monotonicity** on ℤ^d. -/
theorem magnetizationΛ_bot_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ)) Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  magnetizationΛ_monotone_ambient_subgraph bot_le Λ p hf i

/-- **`⊥` ≤ `latticeGraph d` magnetizationAlongExhaustion monotonicity**
per stage on ℤ^d. -/
theorem magnetizationAlongExhaustion_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_monotone_ambient_subgraph bot_le Λ p hf i n

/-- **`⊥` ≤ `latticeGraph d` magnetizationInfinite monotonicity** on ℤ^d. -/
theorem magnetizationInfinite_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (⊥ : SimpleGraph (Fin d → ℤ)) Λ p i
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_monotone_ambient_subgraph bot_le Λ p hf i

/-- **`⊥` ≤ `latticeGraph d` spontaneousCorrelation monotonicity** on ℤ^d. -/
theorem spontaneousCorrelation_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (⊥ : SimpleGraph (Fin d → ℤ)) Λ J β A
      ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  spontaneousCorrelation_monotone_ambient_subgraph bot_le Λ hJ hβ A

/-- **`⊥` ≤ `latticeGraph d` spontaneousMagnetization monotonicity** on ℤ^d. -/
theorem spontaneousMagnetization_bot_le_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (⊥ : SimpleGraph (Fin d → ℤ))
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (⊥ : SimpleGraph (Fin d → ℤ)) Λ J β i
      ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousMagnetization_monotone_ambient_subgraph bot_le Λ hJ hβ i

/-- **ℤ^d truncated2Infinite nonneg** (general). -/
theorem truncated2Infinite_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i j :=
  truncated2Infinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf i j

/-- **ℤ^d truncated2Infinite nonneg at distinct sites**. -/
theorem truncated2Infinite_latticeGraph_nonneg_of_ne
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i j :=
  truncated2Infinite_nonneg_of_ne (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf hij

/-- **ℤ^d truncated2Infinite nonneg on diagonal**. -/
theorem truncated2Infinite_latticeGraph_nonneg_of_eq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ truncated2Infinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p i i :=
  truncated2Infinite_nonneg_of_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf i

/-- **ℤ^d `truncated2Infinite` apply** (definitional). -/
theorem truncated2Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j} :=
  truncated2Infinite_apply (IsingModel.latticeGraph d) Λ p i j

/-- **ℤ^d `truncated4Infinite` apply** (definitional, pair-split form). -/
theorem truncated4Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j, k, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, l}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i, l}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, k} :=
  truncated4Infinite_apply (IsingModel.latticeGraph d) Λ p i j k l

/-- **ℤ^d `truncated3Infinite` apply** (definitional). -/
theorem truncated3Infinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {i, k}
        - correlationInfinite (IsingModel.latticeGraph d) Λ p {k}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j}
        + 2 * correlationInfinite (IsingModel.latticeGraph d) Λ p {i}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {j}
          * correlationInfinite (IsingModel.latticeGraph d) Λ p {k} :=
  truncated3Infinite_apply (IsingModel.latticeGraph d) Λ p i j k

/-- **ℤ^d `truncated2Infinite ≤ correlationInfinite {i, j}`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_correlationInfinite
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {i, j} :=
  truncated2Infinite_le_correlationInfinite (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `truncated2Infinite ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ≤ 1 :=
  truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `-1 ≤ truncated2Infinite`** (ferromagnetic). -/
theorem neg_one_le_truncated2Infinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    -1 ≤ truncated2Infinite (IsingModel.latticeGraph d) Λ p i j :=
  neg_one_le_truncated2Infinite (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `|truncated2Infinite| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2Infinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    |truncated2Infinite (IsingModel.latticeGraph d) Λ p i j| ≤ 1 :=
  abs_truncated2Infinite_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d `truncated2Infinite² ≤ 1`** (ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j ^ 2 ≤ 1 :=
  truncated2Infinite_sq_le_one (IsingModel.latticeGraph d) Λ p hf i j

/-- **ℤ^d truncated 2-point function vanishes at `J = 0`, `i ≠ j`**
(ferromagnetic). -/
theorem truncated2Infinite_latticeGraph_J_zero_of_ne
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j : Fin d → ℤ} (hij : i ≠ j) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 :=
  truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ h β hf hij

/-- **ℤ^d truncated 2-point function at `J = 0` diagonal**
(ferromagnetic): `truncated2Infinite ⟨0,h,β⟩ i i = tanh(β·h) · (1 − tanh(β·h))`.
Concrete wrapper for `truncated2Infinite_J_zero_diagonal`. -/
theorem truncated2Infinite_latticeGraph_J_zero_diagonal
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  truncated2Infinite_J_zero_diagonal (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d truncated 2-point function vanishes at `β = 0`**. -/
theorem truncated2Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 :=
  truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j

/-- **ℤ^d truncated2Infinite symmetry in (i, j)**. -/
theorem truncated2Infinite_latticeGraph_symm
    (d : ℕ) (p : IsingParams ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i j
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p j i :=
  truncated2Infinite_symm (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p i j

/-- **ℤ^d truncated2Infinite at h=0**: collapses to `correlationInfinite ... {i, j}`. -/
theorem truncated2Infinite_latticeGraph_h_zero
    (d : ℕ) (J β : ℝ) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ i j
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ {i, j} :=
  truncated2Infinite_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β i j

/-- **ℤ^d truncated3Infinite β=0 site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k

/-- **ℤ^d truncated3Infinite J=0 pairwise distinct site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hjk hik

/-- **ℤ^d truncated3Infinite J=0 pair coincidence vanishes**
(`i = j ≠ k`): concrete wrapper for
`truncated3Infinite_J_zero_of_pair_coincidence` (#742). -/
theorem truncated3Infinite_latticeGraph_J_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k = 0 :=
  truncated3Infinite_J_zero_of_pair_coincidence (IsingModel.latticeGraph d) Λ
    h β hf hik

/-- **ℤ^d truncated3Infinite J=0 all-coincident closed form**:
`truncated3Infinite ⟨0,h,β⟩ i i i = t·(1-t)·(1-2t)` with `t = tanh(β·h)`.
Concrete wrapper for `truncated3Infinite_J_zero_all_coincident` (#743). -/
theorem truncated3Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h))
          * (1 - 2 * Real.tanh (β * h)) :=
  truncated3Infinite_J_zero_all_coincident (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d truncated4Infinite β=0 site-wise**: `= 0`. -/
theorem truncated4Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 :=
  truncated4Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k l

/-- **ℤ^d truncated4Infinite J=0 pairwise distinct site-wise**: `= -2·tanh(β·h)^4`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_pairwise_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_pairwise_distinct (IsingModel.latticeGraph d) Λ
    h β hf hij hik hil hjk hjl hkl

/-- **ℤ^d truncated4Infinite J=0 one-pair coincidence** (#745). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_one_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k l : Fin d → ℤ}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k l
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_one_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik hil hkl

/-- **ℤ^d truncated4Infinite J=0 two-pair coincidence** (#746). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_two_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k k
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_two_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik

/-- **ℤ^d truncated4Infinite J=0 triple coincidence** (#747):
`t² − 3·t³`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_triple_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i l : Fin d → ℤ} (hil : i ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i l
      = Real.tanh (β * h) ^ 2 - 3 * Real.tanh (β * h) ^ 3 :=
  truncated4Infinite_J_zero_of_triple_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hil

/-- **ℤ^d truncated4Infinite J=0 all-coincident** (#748): `t − 3·t²`. -/
theorem truncated4Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i i
      = Real.tanh (β * h) - 3 * Real.tanh (β * h) ^ 2 :=
  truncated4Infinite_J_zero_all_coincident
    (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d truncated3Infinite h=0 pair coincidence** (#750):
`truncated3Infinite ⟨J,0,β⟩ i i k = correlationInfinite ⟨J,0,β⟩ {i,k}`
for `i ≠ k` (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_h_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i k
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, k} :=
  truncated3Infinite_h_zero_of_pair_coincidence
    (IsingModel.latticeGraph d) Λ J β hik

/-- **ℤ^d truncated3Infinite h=0 all-coincident vanishes** (#750). -/
theorem truncated3Infinite_latticeGraph_h_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i i = 0 :=
  truncated3Infinite_h_zero_all_coincident
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d truncated3Infinite nonpos** (GHS) site-wise (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_nonpos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : Fin d → ℤ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d) Λ p hf hij hjk hik

/-- **ℤ^d truncated4Infinite nonpos at h=0** (Lebowitz) site-wise. -/
theorem truncated4Infinite_latticeGraph_nonpos_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : Fin d → ℤ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d) Λ J β hf
    hij hik hil hjk hjl hkl

/-- **ℤ^d truncated3Infinite at h=0 vanishes** site-wise, pairwise distinct. -/
theorem truncated3Infinite_latticeGraph_h_zero_of_distinct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i j k : Fin d → ℤ}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i j k = 0 :=
  truncated3Infinite_h_zero_of_distinct (IsingModel.latticeGraph d) Λ J β
    hij hjk hik

/-- **ℤ^d truncated2Infinite exhaustion-independence**. -/
theorem truncated2Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
      = truncated2Infinite (IsingModel.latticeGraph d) Λ' p i j :=
  truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j

/-- **ℤ^d truncated3Infinite exhaustion-independence**. -/
theorem truncated3Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k
      = truncated3Infinite (IsingModel.latticeGraph d) Λ' p i j k :=
  truncated3Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j k

/-- **ℤ^d truncated4Infinite exhaustion-independence**. -/
theorem truncated4Infinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l
      = truncated4Infinite (IsingModel.latticeGraph d) Λ' p i j k l :=
  truncated4Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf
    i j k l

/-- **ℤ^d correlationInfinite ≤ 1** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A ≤ 1 :=
  correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationInfinite ≥ 0** (any Exhaustion, ferromagnetic). -/
theorem correlationInfinite_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf A

/-- **Exhaustion-independence of `correlationInfinite` on ℤ^d**
(GJ Thm 4.2.3 corollary): any two exhaustions of `Fin d → ℤ` yield
the same ∞-vol correlation. -/
theorem correlationInfinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      = correlationInfinite (IsingModel.latticeGraph d) Λ' p A :=
  correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf A

/-- **h-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.4):
for `0 ≤ J, 0 < β`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`h ∈ Ici 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **β-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.4):
for `0 ≤ J, 0 ≤ h`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`β ∈ Ioi 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh A

/-- **J-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.1):
for `0 ≤ h, 0 < β`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`J ∈ Ici 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ A

/-- **GKS-II at ∞-volume on ℤ^d**: for ferromagnetic `p` and any
`A, B : Finset (Fin d → ℤ)`,

`correlationInfinite ... p A · correlationInfinite ... p B
  ≤ correlationInfinite ... p (A ∆ B)`.

Concrete ℤ^d specialisation of `correlationInfinite_gks_second`
(Glimm–Jaffe §4.2 Thm 4.2.3). -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_gks_second
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A
      * correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p B
      ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (A ∆ B) :=
  correlationInfinite_gks_second (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A B


end Ambient
end IsingModel
