import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance

/-!
# Concrete translation invariance for the ℤ^d Ising correlation

Apply the abstract `correlationInfinite_vaddFinset_of_translationInvariant`
theorem (`TranslationInvariance.lean`, PR #251) to the physical
`d`-dimensional Ising setup
`(IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`:

* `isTranslationInvariant_latticeGraph` (PR #244) supplies the
  `IsTranslationInvariant (Fin d → ℤ) (latticeGraph d)` instance.
* `cubicExhaustion d` (PR #245) supplies the ambient exhaustion.
* The `Fintype (inducedGraph (latticeGraph d) Λ).edgeSet` instance
  (PR #246) supplies the Fintype hypothesis for arbitrary `Λ`.

## Main theorems

* `correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`:
  `correlationInfinite (latticeGraph d) (cubicExhaustion d) p
  (vaddFinset t A) = correlationInfinite ... p A` (ferromagnetic).
* `magnetizationInfinite_latticeGraph_cubicExhaustion_translation`:
  single-site specialization.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 68.
-/

namespace IsingModel

namespace Ambient

/-- **Translation invariance of the ∞-volume Ising correlation on ℤ^d**:
for ferromagnetic `p` and any translation `t : Fin d → ℤ`,

`correlationInfinite (latticeGraph d) (cubicExhaustion d) p (vaddFinset t A)
  = correlationInfinite (latticeGraph d) (cubicExhaustion d) p A`.

Direct application of `correlationInfinite_vaddFinset_of_translationInvariant`
(PR #251) with the `IsTranslationInvariant (Fin d → ℤ) (latticeGraph d)`
instance (PR #244) and the concrete Fintype instance on induced-lattice
edge sets (PR #246). -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (vaddFinset t A)
      = correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A := by
  exact correlationInfinite_vaddFinset_of_translationInvariant
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) t p hf A

/-- **Translation invariance of the ∞-volume Ising magnetization on ℤ^d**:
for ferromagnetic `p` and any translation `t : Fin d → ℤ`,

`magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p (t + i)
  = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p i`.

Specialization of `correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`
at `A = {i}`; uses that `vaddFinset t {i} = {t +ᵥ i}`. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (t +ᵥ i)
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p i := by
  unfold magnetizationInfinite
  -- `correlationInfinite G Λ p {t +ᵥ i} = correlationInfinite G Λ p (vaddFinset t {i})`.
  rw [show ({t +ᵥ i} : Finset (Fin d → ℤ)) = vaddFinset t {i} from
        (vaddFinset_singleton t i).symm]
  exact correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d t p hf {i}

/-- **ℤ^d truncated 2-point translation invariance**: for ferromagnetic `p`,
`truncated2Infinite (latticeGraph d) (cubicExhaustion d) p (t + i) (t + j)
  = truncated2Infinite ... p i j`.

Direct application of `truncated2Infinite_translation` (PR #253). -/
theorem truncated2Infinite_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (t +ᵥ i) (t +ᵥ j)
      = truncated2Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p i j :=
  truncated2Infinite_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p hf i j

/-- **ℤ^d truncated 3-point (Ursell) translation invariance**. -/
theorem truncated3Infinite_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (t +ᵥ i) (t +ᵥ j) (t +ᵥ k)
      = truncated3Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p i j k :=
  truncated3Infinite_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p hf i j k

/-- **ℤ^d Lebowitz 4-point translation invariance**. -/
theorem truncated4Infinite_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (t +ᵥ i) (t +ᵥ j) (t +ᵥ k) (t +ᵥ l)
      = truncated4Infinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p i j k l :=
  truncated4Infinite_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p hf i j k l

/-- **Site-independence of ℤ^d ∞-vol magnetization**:
for ferromagnetic `p` and any two sites `i, j : Fin d → ℤ`,

`magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p i
  = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p j`.

Consequence of translation invariance: set `t := j - i`; then
`t + i = j` and `magnetizationInfinite_..._translation` gives the
equality. Physical content: on the translation-invariant ℤ^d lattice,
the magnetization is spatially uniform. -/
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_eq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p j := by
  -- Apply `magnetizationInfinite_..._translation` with `t := j - i`.
  have h := magnetizationInfinite_latticeGraph_cubicExhaustion_translation
    d (j - i) p hf i
  -- `h : magnetizationInfinite ... ((j - i) +ᵥ i) = magnetizationInfinite ... i`.
  -- On the self-action, `(j - i) +ᵥ i = (j - i) + i = j`.
  have hvadd : (j - i) +ᵥ i = j := by
    change (j - i) + i = j
    abel
  rw [hvadd] at h
  exact h.symm

/-- **Site-independence of ℤ^d spontaneous magnetization**. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i j : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β j := by
  -- Same trick: `t := j - i`.
  have h := spontaneousMagnetization_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (j - i) hJ hβ i
  have hvadd : (j - i) +ᵥ i = j := by
    change (j - i) + i = j
    abel
  rw [hvadd] at h
  exact h.symm

/-- **ℤ^d free-energy shift invariance**:
`freeEnergyInfinite (latticeGraph d) ((cubicExhaustion d).shift t) p
  = freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_shift
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p

/-! ## Site-independent magnetization on ℤ^d -/

/-- **Uniform magnetization on ℤ^d**: since the ∞-vol magnetization is
site-independent on the translation-invariant ℤ^d lattice (PR #257),
we package the value at `0` as a scalar `uniformMagnetization d p`.

`uniformMagnetization d p := magnetizationInfinite (latticeGraph d)
(cubicExhaustion d) p 0`. -/
noncomputable def uniformMagnetization (d : ℕ) (p : IsingParams ℝ) : ℝ :=
  magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **Bridge**: for ferromagnetic `p` and any site `i : Fin d → ℤ`,
`magnetizationInfinite ... p i = uniformMagnetization d p`.

Immediate from `magnetizationInfinite_latticeGraph_cubicExhaustion_eq`
(PR #257) at `i, 0`. -/
@[simp]
theorem magnetizationInfinite_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p i
      = uniformMagnetization d p :=
  magnetizationInfinite_latticeGraph_cubicExhaustion_eq d p hf i 0

/-- **Nonnegativity of `uniformMagnetization`** (ferromagnetic).
Specialization of the abstract `magnetizationInfinite_nonneg`. -/
theorem uniformMagnetization_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ uniformMagnetization d p :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0

/-- **Upper bound on `uniformMagnetization`**:
`uniformMagnetization d p ≤ 1`. -/
theorem uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **Uniform spontaneous magnetization on ℤ^d**: by site-independence
of spontaneous magnetization on the translation-invariant ℤ^d lattice
(PR #257), we package the value at `0` as a scalar.

`uniformSpontaneousMagnetization d J β := spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
noncomputable def uniformSpontaneousMagnetization
    (d : ℕ) (J β : ℝ) : ℝ :=
  spontaneousMagnetization (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β 0

/-- **Bridge**: for `0 ≤ J`, `0 < β`, and any site `i : Fin d → ℤ`,
`spontaneousMagnetization ... J β i = uniformSpontaneousMagnetization d J β`.

Immediate from `spontaneousMagnetization_latticeGraph_cubicExhaustion_eq`
(PR #257). -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq_uniform
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_latticeGraph_cubicExhaustion_eq d hJ hβ i 0

/-- **Nonnegativity of `uniformSpontaneousMagnetization`**. -/
theorem uniformSpontaneousMagnetization_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    0 ≤ uniformSpontaneousMagnetization d J β :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **Upper bound on `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β ≤ 1`. -/
theorem uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`uniformMagnetization` at `β = 0`**:
`uniformMagnetization d ⟨J, h, 0⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_beta_zero` at site `0`:
at infinite temperature (`β = 0`) all spin correlations vanish, in
particular the magnetization. No ferromagnetic hypothesis needed. -/
theorem uniformMagnetization_beta_zero
    (d : ℕ) (J h : ℝ) :
    uniformMagnetization d (⟨J, h, 0⟩ : IsingParams ℝ) = 0 :=
  magnetizationInfinite_beta_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J h 0

/-- **`uniformMagnetization` at `J = 0`**:
`uniformMagnetization d ⟨0, h, β⟩ = tanh(β · h)` (ferromagnetic).

Concrete specialisation of `magnetizationInfinite_J_zero` at site `0`
on the `(latticeGraph d, cubicExhaustion d)` pair. Non-interacting
slice: at `J = 0` the Ising Hamiltonian has no coupling, so each site
is an independent two-state system with Boltzmann weight `exp(β h s)`,
giving `M = tanh(β h)`. -/
theorem uniformMagnetization_J_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    uniformMagnetization d (⟨0, h, β⟩ : IsingParams ℝ) = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) h β hf 0

/-- **Z₂ symmetry at `h = 0`**: `uniformMagnetization d ⟨J, 0, β⟩ = 0`.

Concrete specialisation of `magnetizationInfinite_zero_at_h_zero` at
site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. At `h = 0`
the finite-volume Ising model is Z₂-symmetric (flip `σ ↦ −σ`), so
the magnetization vanishes stage-by-stage, hence at ∞-vol. -/
theorem uniformMagnetization_zero_at_h_zero
    (d : ℕ) (J β : ℝ) :
    uniformMagnetization d ⟨J, 0, β⟩ = 0 :=
  magnetizationInfinite_zero_at_h_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β 0

/-- **Right-limit** `uniformMagnetization` → `uniformSpontaneousMagnetization`
as `h → 0⁺`.

Concrete specialization of the abstract
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`
at site `0` on the `(latticeGraph d, cubicExhaustion d)` pair. Realises
the spontaneous magnetization as the right limit of the uniform
(site-independent) magnetization as the external field `h` approaches
zero from above. -/
theorem tendsto_uniformMagnetization_uniformSpontaneousMagnetization_nhdsGT
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (uniformSpontaneousMagnetization d J β)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ 0

/-- **`uniformSpontaneousMagnetization ≤ uniformMagnetization` at `h > 0`**:
for `0 ≤ J`, `0 < β`, `0 < h`,

`uniformSpontaneousMagnetization d J β
  ≤ uniformMagnetization d ⟨J, h, β⟩`.

Direct specialization of `spontaneousMagnetization_le_magnetizationInfinite`
at site `0` combined with the uniform recasts. The Ising parameter
record `⟨J, h, β⟩` with `0 < h` is ferromagnetic, so the
`uniformMagnetization` bridge applies. -/
theorem uniformSpontaneousMagnetization_le_uniformMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) :
    uniformSpontaneousMagnetization d J β
      ≤ uniformMagnetization d ⟨J, h, β⟩ :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ hh 0

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

/-! ## Basic bounds on the ℤ^d two-point functions -/

/-- **Nonnegativity of `twoPointFunction`** (GKS-I).
`0 ≤ twoPointFunction d p r`. -/
theorem twoPointFunction_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ twoPointFunction d p r :=
  correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf {(0 : Fin d → ℤ), r}

/-- **Upper bound on `twoPointFunction`** (boundedness of correlation).
`twoPointFunction d p r ≤ 1`. -/
theorem twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ≤ 1 :=
  correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **Nonnegativity of `truncated2TwoPoint`** (GKS-II).
`0 ≤ truncated2TwoPoint d p r`. -/
theorem truncated2TwoPoint_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ truncated2TwoPoint d p r :=
  truncated2Infinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0 r

/-- **Two-point function bounded below by magnetization squared**:
for ferromagnetic `p` and any `r : Fin d → ℤ`,

`(magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0)^2
  ≤ twoPointFunction d p r`.

Proof: from `truncated2TwoPoint_nonneg` (GKS-II) and the identity
`truncated2TwoPoint d p r = twoPointFunction d p r − M²` (PR #261),
we get `0 ≤ twoPointFunction d p r − M²`, hence `M² ≤ twoPointFunction
d p r`. This is a classical physical bound: the 2-point function at
infinite volume is at least as large as the squared magnetization. -/
theorem twoPointFunction_ge_magnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p 0)^2
      ≤ twoPointFunction d p r := by
  have h_nonneg := truncated2TwoPoint_nonneg d p hf r
  have h_identity := truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq
    d p hf r
  linarith [h_identity.symm ▸ h_nonneg]

/-- **Symmetry of `truncated3TwoPoint` under `(r, s)` swap**:
`truncated3TwoPoint d p r s = truncated3TwoPoint d p s r`.

Reduces to the pairwise-symmetry of the Ursell 3-point function in
its last two arguments, via unfolding and commutativity of the
relevant Finset literals and products. -/
theorem truncated3TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s = truncated3TwoPoint d p s r := by
  unfold truncated3TwoPoint truncated3Infinite
  -- `{0, r, s} = {0, s, r}` (unordered).
  have h_triple : ({(0 : Fin d → ℤ), r, s} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_triple, h_rs]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(r, s)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u`.

From the Lebowitz 4-point definition: swapping `j ↔ k` in
`truncated4Infinite ... i j k l` permutes the three pair-products,
yielding the same sum. -/
theorem truncated4TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r, u} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_rs]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(s, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s`.

Same Lebowitz-permutation argument applied to swap of `k ↔ l`. -/
theorem truncated4TwoPoint_symm_su
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), r, u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_su : ({s, u} : Finset (Fin d → ℤ)) = {u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_su]
  ring

/-! ## `uniformMagnetization` recasts -/

/-- **`twoPointFunction` at `r = 0` equals `uniformMagnetization`**
(convenience recast). Combines `twoPointFunction_zero` with the
definition of `uniformMagnetization`. -/
theorem twoPointFunction_zero_eq_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    twoPointFunction d p 0 = uniformMagnetization d p :=
  twoPointFunction_zero d p

/-- **`truncated2TwoPoint = twoPointFunction − (uniformMagnetization)²`**
(convenience recast). -/
theorem truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r
      = twoPointFunction d p r - (uniformMagnetization d p)^2 :=
  truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq d p hf r

/-- **`twoPointFunction ≥ (uniformMagnetization)²`** (convenience recast). -/
theorem twoPointFunction_ge_uniformMagnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (uniformMagnetization d p)^2 ≤ twoPointFunction d p r :=
  twoPointFunction_ge_magnetization_sq d p hf r

/-! ## Concrete Lebowitz / GHS inequalities on ℤ^d -/

/-- **GHS `U_3 ≤ 0` on ℤ^d** (Glimm–Jaffe §4.3 Cor 4.3.4): for
ferromagnetic `p` and pairwise distinct `r, s : Fin d → ℤ`
(with both non-zero to ensure distinctness from the anchor `0`),
`truncated3TwoPoint d p r s ≤ 0`.

Direct application of `truncated3Infinite_nonpos` at `i = 0, j = r, k = s`
under the three distinctness hypotheses `0 ≠ r, r ≠ s, 0 ≠ s`. -/
theorem truncated3TwoPoint_nonpos_of_distinct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {r s : Fin d → ℤ} (hr : (0 : Fin d → ℤ) ≠ r)
    (hrs : r ≠ s) (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d p r s ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf hr hrs hs

/-- **Lebowitz `U_4 ≤ 0` on ℤ^d at `h = 0`** (Glimm–Jaffe §4.3 Cor 4.3.3):
for ferromagnetic `⟨J, 0, β⟩` and pairwise distinct `r, s, u : Fin d → ℤ`
(all three non-zero + pairwise distinct),
`truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0`.

Direct application of `truncated4Infinite_nonpos_h_zero` at
`i = 0, j = r, k = s, l = u`. -/
theorem truncated4TwoPoint_nonpos_h_zero_of_distinct
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf hr hs hu hrs hru hsu

end Ambient

end IsingModel
