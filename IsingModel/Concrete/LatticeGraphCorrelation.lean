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

open scoped symmDiff

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

/-! ## Concrete `spontaneousCorrelation` on ℤ^d -/

/-- **Nonnegativity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    0 ≤ spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **Upper bound on `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A ≤ 1 :=
  spontaneousCorrelation_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **ℤ^d `spontaneousMagnetization ≤ magnetizationInfinite`** at positive `h`. -/
theorem spontaneousMagnetization_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  spontaneousMagnetization_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ hJ hβ hh i

/-- **Infimum bound** `spontaneousCorrelation ≤ correlationInfinite ⟨J, h, β⟩`
for `h > 0` on ℤ^d. -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ hh A

/-- **ℤ^d `spontaneousCorrelation ≤ correlationInfinite`** for `h > 0`
(any Exhaustion). -/
theorem spontaneousCorrelation_le_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {h : ℝ} (hh : 0 < h)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  spontaneousCorrelation_le_correlationInfinite (IsingModel.latticeGraph d)
    Λ hJ hβ hh A

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hβ A

/-- **Translation invariance of `spontaneousCorrelation` on ℤ^d**:
for `0 ≤ J`, `0 < β` and any `t : Fin d → ℤ`,
`spontaneousCorrelation ... J β (vaddFinset t A) = spontaneousCorrelation ... J β A`. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β (vaddFinset t A)
      = spontaneousCorrelation (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t hJ hβ A

/-- **J-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ A

/-- **β-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ A

/-- **Exhaustion-independence of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A
      = spontaneousCorrelation (IsingModel.latticeGraph d) Λ' J β A :=
  spontaneousCorrelation_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ A

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

/-- **ℤ^d correlationΛ volume-monotonicity**:
`A ⊆ Λ₁ ⊆ Λ₂ ⇒ ⟨σ^A⟩_{Λ₁} ≤ ⟨σ^A⟩_{Λ₂}` for ferromagnetic `p`. -/
theorem correlationΛ_latticeGraph_monotone_volume
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    correlationΛ (IsingModel.latticeGraph d) Λ₁ p (liftFinset A hA)
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ₂ p
          (liftFinset A (hA.trans h12)) :=
  correlationΛ_monotone_volume (IsingModel.latticeGraph d) h12 p hf hA

/-- **ℤ^d partitionFunctionΛ positivity** per finite volume. -/
theorem partitionFunctionΛ_latticeGraph_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    0 < partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_pos (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `|correlationΛ| ≤ 1`** per finite volume. -/
theorem abs_correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |correlationΛ (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≤ 1** per finite volume. -/
theorem correlationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ≤ 1 :=
  correlationΛ_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d correlationΛ ≥ 0** per finite volume (ferromagnetic). -/
theorem correlationΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (A : Finset (↑Λ : Type _)) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_nonneg (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d freeEnergyAlongExhaustion_apply unfolding**. -/
@[simp]
theorem freeEnergyAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = freeEnergyΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  freeEnergyAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion_apply unfolding**. -/
@[simp]
theorem partitionFunctionAlongExhaustion_latticeGraph_apply
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p :=
  partitionFunctionAlongExhaustion_apply (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d freeEnergyAlongExhaustion = log Z / |Λ|** (log-bridge). -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_log_div_card
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      = (Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d `correlationAlongExhaustion` is ≤ 1** per stage (unconditional).
Concrete specialization of `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationAlongExhaustion` is ≥ 0** per stage (ferromagnetic).
Concrete specialization of `correlationAlongExhaustion_nonneg`. -/
theorem correlationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf A n

/-- **ℤ^d `correlationInfinite` on the empty site set = 1** (any Exhaustion). -/
@[simp]
theorem correlationInfinite_latticeGraph_empty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `correlationΛ` vanishes at `β = 0`** for nonempty `A : Finset ↑Λ`. -/
theorem correlationΛ_latticeGraph_beta_zero_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_beta_zero_vanish_of_nonempty (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d `correlationΛ` vanishes at `J = h = 0`** for nonempty `A`. -/
theorem correlationΛ_latticeGraph_zero_params_vanish_of_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationΛ_zero_params_vanish_of_nonempty (IsingModel.latticeGraph d) Λ β A hA

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `β = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_beta_zero_vanish (IsingModel.latticeGraph d)
    Λ J h A hA n

/-- **ℤ^d `correlationAlongExhaustion` vanishes at `J = h = 0`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (β : ℝ) (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_zero_params_vanish (IsingModel.latticeGraph d)
    Λ β A hA n

/-- **ℤ^d `partitionFunctionΛ_apply`** unfolding. -/
theorem partitionFunctionΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  partitionFunctionΛ_apply (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `correlationΛ_apply`** unfolding. -/
theorem correlationΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  correlationΛ_apply (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `freeEnergyΛ_apply`** unfolding. -/
theorem freeEnergyΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  freeEnergyΛ_apply (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `magnetizationΛ_monotone_ambient_subgraph`**:
`G₁ ≤ G₂ ⇒ M_{Λ,G₁}(i) ≤ M_{Λ,G₂}(i)` (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph G₁ Λ).edgeSet]
    [Fintype (Ambient.inducedGraph G₂ Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : ↑Λ) :
    magnetizationΛ G₁ Λ p i ≤ magnetizationΛ G₂ Λ p i :=
  magnetizationΛ_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion_monotone_ambient_subgraph`**
per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion G₁ Λ p i n
      ≤ magnetizationAlongExhaustion G₂ Λ p i n :=
  magnetizationAlongExhaustion_monotone_ambient_subgraph h Λ p hf i n

/-- **ℤ^d `magnetizationInfinite_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (h : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite G₁ Λ p i ≤ magnetizationInfinite G₂ Λ p i :=
  magnetizationInfinite_monotone_ambient_subgraph h Λ p hf i

/-- **ℤ^d `spontaneousCorrelation_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation G₁ Λ J β A
      ≤ spontaneousCorrelation G₂ Λ J β A :=
  spontaneousCorrelation_monotone_ambient_subgraph hG Λ hJ hβ A

/-- **ℤ^d `-1 ≤ spontaneousCorrelation`** (ferromagnetic). -/
theorem neg_one_le_spontaneousCorrelation_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    -1 ≤ spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A :=
  neg_one_le_spontaneousCorrelation (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `|spontaneousCorrelation| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousCorrelation_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    |spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A| ≤ 1 :=
  abs_spontaneousCorrelation_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousCorrelation² ≤ 1`** (ferromagnetic). -/
theorem spontaneousCorrelation_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A ^ 2 ≤ 1 :=
  spontaneousCorrelation_sq_le_one (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d `spontaneousMagnetization_monotone_ambient_subgraph`**
(ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_monotone_ambient_subgraph
    (d : ℕ) {G₁ G₂ : SimpleGraph (Fin d → ℤ)} (hG : G₁ ≤ G₂)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph G₂ (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization G₁ Λ J β i
      ≤ spontaneousMagnetization G₂ Λ J β i :=
  spontaneousMagnetization_monotone_ambient_subgraph hG Λ hJ hβ i

/-- **ℤ^d `magnetizationΛ² ≤ 1`**. -/
theorem magnetizationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `magnetizationAlongExhaustion² ≤ 1`** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ^ 2 ≤ 1 := by
  have h := abs_magnetizationAlongExhaustion_le_one
    (IsingModel.latticeGraph d) Λ p i n
  have : |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ^ 2
      ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **ℤ^d `magnetizationInfinite² ≤ 1`** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationΛ` at `J = 0` closed form**:
`correlationΛ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationΛ_J_zero (IsingModel.latticeGraph d) Λ h β A

/-- **ℤ^d `correlationΛ ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationΛ_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (↑Λ : Type _)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationΛ_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A

/-- **ℤ^d `correlationInfinite ≥ tanh(β·h)^|A|`** (ferromagnetic). -/
theorem correlationInfinite_latticeGraph_ge_tanh_pow_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d) Λ hJ hh hβ A


/-- **ℤ^d `magnetizationΛ ≥ tanh(β·h)`** (ferromagnetic). -/
theorem magnetizationΛ_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : ↑Λ) :
    Real.tanh (β * h)
      ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationΛ_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i

/-- **ℤ^d `magnetizationInfinite ≥ tanh(β·h)`** (ferromagnetic, any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_ge_tanh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (i : Fin d → ℤ) :
    Real.tanh (β * h)
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d) Λ hJ hh hβ i


/-- **ℤ^d `correlationAlongExhaustion` at `J = 0`** per stage (on-stage):
`A ⊆ Λ.volume n ⇒ = tanh(β·h)^|A|`. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_of_subset
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) {A : Finset (Fin d → ℤ)} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_of_subset (IsingModel.latticeGraph d) Λ h β hAn

/-- **ℤ^d `correlationAlongExhaustion` at `J = 0` is eventually constant
at `tanh(β·h)^|A|`**. -/
theorem correlationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card :=
  correlationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β A


/-- **ℤ^d correlationΛ_empty = 1** per finite volume. -/
@[simp]
theorem correlationΛ_latticeGraph_empty
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    correlationΛ (IsingModel.latticeGraph d) Λ p ∅ = 1 :=
  correlationΛ_empty (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d correlationAlongExhaustion_empty = 1** per stage. -/
@[simp]
theorem correlationAlongExhaustion_latticeGraph_empty
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p ∅ n = 1 :=
  correlationAlongExhaustion_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d correlationAlongExhaustion of_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n
      = correlationΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p (liftFinset A hA) :=
  correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion of_not_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_not_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : ¬ A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n = 0 :=
  correlationAlongExhaustion_of_not_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion stage-index Monotone**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationΛ_gks_second** (GKS-II at finite volume). -/
theorem correlationΛ_latticeGraph_gks_second
    (d : ℕ) {Λ : Finset (Fin d → ℤ)}
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A B : Finset (Fin d → ℤ)} (hA : A ⊆ Λ) (hB : B ⊆ Λ) :
    ∃ hAB : A ∆ B ⊆ Λ,
      correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset A hA)
        * correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset B hB)
        ≤ correlationΛ (IsingModel.latticeGraph d) Λ p (liftFinset (A ∆ B) hAB) := by
  have hAB : A ∆ B ⊆ Λ := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with ⟨hxA, _⟩ | ⟨hxB, _⟩
    · exact hA hxA
    · exact hB hxB
  refine ⟨hAB, ?_⟩
  exact correlationΛ_gks_second (IsingModel.latticeGraph d) p hf hA hB

/-- **ℤ^d per-Λ h-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d per-Λ β-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {J : ℝ} (hJ : 0 ≤ J)
    {h : ℝ} (hh : 0 ≤ h) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A

/-- **ℤ^d per-Λ J-monotonicity of `correlationΛ`**. -/
theorem correlationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) {h : ℝ} (hh : 0 ≤ h)
    {β : ℝ} (hβ : 0 < β) (A : Finset (↑Λ : Type _)) :
    MonotoneOn
      (fun J : ℝ => correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

/-- **ℤ^d per-stage h-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h₁, β⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h₂, β⟩ A n :=
  correlationAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A hh₁ hh₁₂ n

/-- **ℤ^d per-stage β-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β₁⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β₂⟩ A n :=
  correlationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh A hβ₁ hβ₁₂ n

/-- **ℤ^d per-stage J-monotonicity of correlationAlongExhaustion**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J₁, h, β⟩ A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J₂, h, β⟩ A n :=
  correlationAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ A hJ₁ hJ₁₂ n

/-- **ℤ^d correlationAlongExhaustion range is bddAbove**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_bddAbove
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddAbove (Set.range (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A)) :=
  correlationAlongExhaustion_bddAbove (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d `|correlationAlongExhaustion| ≤ 1` eventually**. -/
theorem abs_correlationAlongExhaustion_latticeGraph_eventually_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    ∀ᶠ n in Filter.atTop,
      |correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_eventually_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A

/-- **ℤ^d correlationAlongExhaustion ≤ 1** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_le_one
    (d : ℕ) (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n ≤ 1 :=
  correlationAlongExhaustion_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p A n

/-- **ℤ^d correlationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A n :=
  correlationAlongExhaustion_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A n

/-- **ℤ^d physical identification: correlationΛ → correlationInfinite**. -/
theorem tendsto_correlationΛ_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ (Ambient.cubicExhaustion d).volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationΛ_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → ciSup** (any Exhaustion). -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d correlationAlongExhaustion → ciSup**. -/
theorem correlationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n)) :=
  correlationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite**. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf A

/-- **ℤ^d correlationAlongExhaustion → correlationInfinite** (any Exhaustion). -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite_latticeGraph_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)
      Filter.atTop
      (nhds (correlationInfinite (IsingModel.latticeGraph d) Λ p A)) :=
  tendsto_correlationAlongExhaustion_correlationInfinite
    (IsingModel.latticeGraph d) Λ p hf A

/-- **ℤ^d log partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1)) :=
  log_partitionFunctionAlongExhaustion_monotone_volume
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion volume-monotonicity** (ferromagnetic):
`partitionFunctionAlongExhaustion` at stage `n+1` is ≥ stage `n`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_volume
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p (n + 1) :=
  partitionFunctionAlongExhaustion_monotone_volume (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_pos
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n

/-- **ℤ^d partitionFunctionAlongExhaustion positivity** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    0 < partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_pos (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d freeEnergyInfinite is strictly positive** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p := by
  refine freeEnergyInfinite_pos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d freeEnergyInfinite is nonnegative** (ferromagnetic). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p :=
  (freeEnergyInfinite_latticeGraph_cubicExhaustion_pos d p hf).le

/-- **ℤ^d freeEnergyInfinite strictly positive** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_pos
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_pos (IsingModel.latticeGraph d) Λ p hf (c := c) hc

/-- **ℤ^d freeEnergyInfinite nonnegative** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_nonneg
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  (freeEnergyInfinite_latticeGraph_pos d Λ p hf hc).le

/-- **log Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n))
      Filter.atTop Filter.atTop :=
  log_partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **Z → ∞ along cubicExhaustion** (ferromagnetic, infinite ℤ^d). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_tendsto_atTop
    (d : ℕ) [Infinite (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n)
      Filter.atTop Filter.atTop :=
  partitionFunctionAlongExhaustion_tendsto_atTop
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf

/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J₁, h, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J₂, h, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h₁, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h₂, β⟩ n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β₁⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β₂⟩ n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

/-- **ℤ^d per-stage J-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    h β hh hβ hJ₁ hJ n

/-- **ℤ^d per-stage h-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh₁ hh n

/-- **ℤ^d per-stage β-monotonicity of partitionFunctionAlongExhaustion** (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    J h hJ hh hβ₁ hβ n

/-- **ℤ^d partitionFunctionΛ h-evenness**:
`Z_{Λ_n}(J, -h, β) = Z_{Λ_n}(J, h, β)` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_neg_h`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n) (⟨J, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_neg_h (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h β

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage:
`Z(Λ_n; J, -h, β) = Z(Λ_n; J, h, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_neg_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0`**:
`Z_{Λ_n}(⟨0, h, β⟩) = (2·cosh(β·h))^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_J_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) h β

/-- **ℤ^d partitionFunctionΛ closed form at `β = 0`**:
`Z_{Λ_n}(⟨J, h, 0⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_beta_zero`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h

/-- **ℤ^d partitionFunctionΛ closed form at `J = 0, h = 0`**:
`Z_{Λ_n}(⟨0, 0, β⟩) = 2^|Λ_n|` on the ℤ^d cubic box.
Concrete specialization of `partitionFunctionΛ_zero_params`. -/
theorem partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionΛ_zero_params (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) β

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0`**:
`log Z_{Λ_n}(⟨0, h, β⟩) = |Λ_n| · log(2·cosh(β·h))` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_J_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, h, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionΛ_J_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) h β

/-- **ℤ^d log_partitionFunctionΛ closed form at `β = 0`**:
`log Z_{Λ_n}(⟨J, h, 0⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_beta_zero`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨J, h, 0⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_beta_zero (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) J h

/-- **ℤ^d log_partitionFunctionΛ closed form at `J = 0, h = 0`**:
`log Z_{Λ_n}(⟨0, 0, β⟩) = |Λ_n| · log 2` on the ℤ^d cubic box.
Concrete specialization of `log_partitionFunctionΛ_zero_params`. -/
theorem log_partitionFunctionΛ_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) (⟨0, 0, β⟩ : IsingParams ℝ))
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_zero_params (IsingModel.latticeGraph d)
    ((Ambient.cubicExhaustion d).volume n) β

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion |h|-form** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d freeEnergyAlongExhaustion |h|-monotonicity** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d freeEnergyAlongExhaustion h-evenness** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion `|h|`-rewrite** per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d freeEnergyAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d) Λ
    J β hJ hβ hh n

/-- **ℤ^d per-stage explicit upper bound on freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card
          + |p.h| * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _))
        / Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n hne

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh n

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J
    (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta
    (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh n

/-- **ℤ^d freeEnergyAlongExhaustion ≥ zero_params**: `f(0,0,β) ≤ f(J,h,β)`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ zero_params** analog. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  partitionFunctionAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d freeEnergyΛ ≥ log(2 cosh βh)** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two_cosh
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two_cosh (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ log 2** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_ge_log_two
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_ge_log_two (IsingModel.latticeGraph d) hne hJ hh hβ

/-- **ℤ^d freeEnergyΛ ≥ 0** (ferromagnetic, nonempty Λ). -/
theorem freeEnergyΛ_latticeGraph_nonneg
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

/-- **ℤ^d freeEnergyΛ closed form at `J = 0`**:
for nonempty `Λ` and any `h, β`,
`freeEnergyΛ ⟨0, h, β⟩ = log(2·cosh(β·h))`. Concrete specialization of
`freeEnergyΛ_J_zero`. -/
theorem freeEnergyΛ_latticeGraph_J_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyΛ_J_zero (IsingModel.latticeGraph d) hne h β

/-- **ℤ^d freeEnergyΛ closed form at `β = 0`**:
for nonempty `Λ` and any `J, h`,
`freeEnergyΛ ⟨J, h, 0⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_beta_zero`. -/
theorem freeEnergyΛ_latticeGraph_beta_zero
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (J h : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_beta_zero (IsingModel.latticeGraph d) hne J h

/-- **ℤ^d freeEnergyΛ closed form at `J = 0, h = 0`**:
for nonempty `Λ` and any `β`,
`freeEnergyΛ ⟨0, 0, β⟩ = log 2`. Concrete specialization of
`freeEnergyΛ_zero_params`. -/
theorem freeEnergyΛ_latticeGraph_zero_params
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty) (β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = Real.log 2 :=
  freeEnergyΛ_zero_params (IsingModel.latticeGraph d) hne β

/-- **ℤ^d freeEnergyΛ h-evenness**:
`freeEnergyΛ ⟨J,-h,β⟩ = freeEnergyΛ ⟨J,h,β⟩` on any ℤ^d-vertex Finset.
Concrete specialization of `freeEnergyΛ_neg_h`. -/
theorem freeEnergyΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ `|h|`-rewrite**:
`freeEnergyΛ ⟨J,h,β⟩ = freeEnergyΛ ⟨J,|h|,β⟩`. Concrete specialization of
`freeEnergyΛ_eq_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d freeEnergyΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and `|h₁| ≤ |h₂|`,
`freeEnergyΛ ⟨J, h₁, β⟩ ≤ freeEnergyΛ ⟨J, h₂, β⟩`. Concrete specialization
of `freeEnergyΛ_monotone_abs_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d freeEnergyΛ J-monotonicity**: for fixed `h ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `J` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_J`. -/
theorem freeEnergyΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ

/-- **ℤ^d freeEnergyΛ h-monotonicity**: for fixed `J ≥ 0`, `β > 0`,
`freeEnergyΛ` is monotone in `h` on `[0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_h`. -/
theorem freeEnergyΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) :=
  freeEnergyΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d freeEnergyΛ β-monotonicity**: for fixed `J ≥ 0`, `h ≥ 0`,
`freeEnergyΛ` is monotone in `β` on `(0, ∞)`. Concrete specialization
of `freeEnergyΛ_monotone_beta`. -/
theorem freeEnergyΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) :=
  freeEnergyΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh

/-- **ℤ^d partitionFunctionΛ J-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_J`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d partitionFunctionΛ h-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d partitionFunctionΛ β-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_beta`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d partitionFunctionΛ `|h|`-rewrite**:
`Z_Λ(J,h,β) = Z_Λ(J,|h|,β)`. Concrete specialization of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d partitionFunctionΛ ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z_Λ(J,h₁,β) ≤ Z_Λ(J,h₂,β)`. Concrete specialization of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d log_partitionFunctionΛ h-evenness**: `log Z_Λ(J,-h,β) = log Z_Λ(J,h,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_neg_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ `|h|`-rewrite**: `log Z_Λ(J,h,β) = log Z_Λ(J,|h|,β)`. -/
theorem log_partitionFunctionΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ))
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d log_partitionFunctionΛ J-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d log_partitionFunctionΛ h-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d log_partitionFunctionΛ β-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d log_partitionFunctionΛ `|h|`-monotonicity** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_abs_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-evenness** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-rewrite** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n)
      = Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion `|h|`-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d partitionFunctionAlongExhaustion `|h|`-rewrite** per stage:
`Z(Λ_n; J, h, β) = Z(Λ_n; J, |h|, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β n

/-- **ℤ^d partitionFunctionAlongExhaustion ferromagnetic `|h|`-monotonicity**
per stage: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`Z(Λ_n; J, h₁, β) ≤ Z(Λ_n; J, h₂, β)`. Concrete specialization of
`partitionFunctionAlongExhaustion_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionAlongExhaustion_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh n

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `freeEnergyΛ = |↑Λ|⁻¹ · log Z_Λ`**. -/
theorem freeEnergyΛ_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ = (Λ.card)⁻¹ · log Z_Λ`** (Finset-card form). -/
theorem freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Λ.card : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyAlongExhaustion = |↑(Λ_n)|⁻¹ · log Z_n`** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion = ((Λ.volume n).card)⁻¹ · log Z_n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d partitionFunctionΛ ≥ (2 cosh βh)^|Λ|** (sharp, ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic, any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log Z_n ≥ 0** (ferromagnetic, any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion ≥ 0** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 2^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ (2 cosh βh)^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 * Real.cosh (p.β * p.h)) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d log Z bound**: `|Λ_n|·log 2 ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d sharp log Z bound**: `|Λ_n|·log(2 cosh βh) ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ)
        * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d sharp log Z_Λ bound**: `|Λ|·log(2 cosh βh) ≤ log Z_Λ` (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion β=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n

/-- **ℤ^d partitionFunctionAlongExhaustion J=h=0 per-stage**: `= 2^|Λ_n|`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=h=0**: `= |Λ_n|·log 2`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2 :=
  log_partitionFunctionAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n

/-- **ℤ^d partitionFunctionAlongExhaustion J=0 per-stage**:
`= (2·cosh(β·h))^|Λ_n|`. Concrete specialization of
`partitionFunctionAlongExhaustion_J_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^
          ((Ambient.cubicExhaustion d).volume n).card :=
  partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J=0**:
`= |Λ_n|·log(2·cosh(β·h))`. Concrete specialization of
`log_partitionFunctionAlongExhaustion_J_zero`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n)
      = (((Ambient.cubicExhaustion d).volume n).card : ℝ)
          * Real.log (2 * Real.cosh (β * h)) :=
  log_partitionFunctionAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n

/-- **ℤ^d freeEnergyAlongExhaustion β=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_beta_zero
    (d : ℕ) (J h : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_beta_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=h=0 per-stage**: `= log 2`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_zero_params
    (d : ℕ) (β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 :=
  freeEnergyAlongExhaustion_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) β n hne

/-- **ℤ^d freeEnergyAlongExhaustion J=0 per-stage**: `= log(2·cosh(β·h))`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_J_zero
    (d : ℕ) (h β : ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyAlongExhaustion_J_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β n hne

/-- **ℤ^d freeEnergyInfinite from convergence**: if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto
    (d : ℕ) (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const
    (d : ℕ) (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite uniform upper bound via BED**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyInfinite_le_uniform_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`**: via BED c=d. -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion
    (d : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)

/-- **ℤ^d per-stage freeEnergyAlongExhaustion upper bound** using BED c = d. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyAlongExhaustion_le_uniform_upper_bound
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p
    (c := (d : ℝ)) ?_ n hne
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Per-stage lower bound on ℤ^d**: `log 2 ≤ freeEnergyAlongExhaustion` for
ferromagnetic + nonempty stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **Sharp per-stage lower bound on ℤ^d**:
`log(2 cosh(βh)) ≤ freeEnergyAlongExhaustion`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **ℤ^d per-stage `log 2 ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `log(2 cosh(βh)) ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `0 ≤ f_n`** (ferromagnetic, nonempty stage, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

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

/-- **Unfolding of `uniformMagnetization`**:
`uniformMagnetization d p = magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0`. -/
theorem uniformMagnetization_apply (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p 0 := rfl

/-- **ℤ^d `uniformMagnetization ≥ tanh(β·h)`** (ferromagnetic). -/
theorem uniformMagnetization_ge_tanh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.tanh (β * h)
      ≤ uniformMagnetization d (⟨J, h, β⟩ : IsingParams ℝ) :=
  magnetizationInfinite_ge_tanh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ 0

/-- **`uniformMagnetization` equals `magnetizationInfinite` under any
Exhaustion** (ferromagnetic): bridges the fixed-`cubicExhaustion` form
to arbitrary Exhaustions via `magnetizationInfinite_indep_exhaustion`. -/
theorem uniformMagnetization_eq_magnetizationInfinite_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    uniformMagnetization d p
      = magnetizationInfinite (IsingModel.latticeGraph d) Λ' p 0 := by
  rw [uniformMagnetization_apply]
  exact magnetizationInfinite_indep_exhaustion (IsingModel.latticeGraph d) _ Λ' p hf 0

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

/-- **`-1 ≤ uniformMagnetization`** unconditionally. Specialization of
`neg_one_le_magnetizationInfinite` at site `0`. -/
theorem neg_one_le_uniformMagnetization
    (d : ℕ) (p : IsingParams ℝ) :
    -1 ≤ uniformMagnetization d p :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`|uniformMagnetization| ≤ 1`** unconditionally. Specialization of
`abs_magnetizationInfinite_le_one` at site `0`. -/
theorem abs_uniformMagnetization_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    |uniformMagnetization d p| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p 0

/-- **`uniformMagnetization² ≤ 1`** unconditionally. Specialization of
`magnetizationInfinite_sq_le_one` at site `0`. -/
theorem uniformMagnetization_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) :
    uniformMagnetization d p ^ 2 ≤ 1 :=
  magnetizationInfinite_sq_le_one (IsingModel.latticeGraph d)
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

/-- **Unfolding of `uniformSpontaneousMagnetization`**:
`uniformSpontaneousMagnetization d J β = spontaneousMagnetization
(latticeGraph d) (cubicExhaustion d) J β 0`. -/
theorem uniformSpontaneousMagnetization_apply (d : ℕ) (J β : ℝ) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β 0 := rfl

/-- **`uniformSpontaneousMagnetization` equals `spontaneousMagnetization`
under any Exhaustion** (ferromagnetic): bridges fixed-`cubicExhaustion`
definition to arbitrary Exhaustions via
`spontaneousMagnetization_indep_exhaustion`. -/
theorem uniformSpontaneousMagnetization_eq_spontaneousMagnetization_any_exhaustion
    (d : ℕ) (Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β 0 := by
  rw [uniformSpontaneousMagnetization_apply]
  exact spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    _ Λ' hJ hβ 0

/-- **J-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ici 0) :=
  spontaneousMagnetization_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ 0

/-- **β-monotonicity of `uniformSpontaneousMagnetization` on ℤ^d**. -/
theorem uniformSpontaneousMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) :
    MonotoneOn
      (fun β : ℝ => uniformSpontaneousMagnetization d J β)
      (Set.Ioi 0) :=
  spontaneousMagnetization_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ 0

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

/-- **`-1 ≤ uniformSpontaneousMagnetization`** (ferromagnetic).
Direct from `uniformSpontaneousMagnetization_nonneg`. -/
theorem neg_one_le_uniformSpontaneousMagnetization
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    -1 ≤ uniformSpontaneousMagnetization d J β := by
  have := uniformSpontaneousMagnetization_nonneg d hJ hβ
  linarith

/-- **`|uniformSpontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_uniformSpontaneousMagnetization_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    |uniformSpontaneousMagnetization d J β| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_uniformSpontaneousMagnetization d hJ hβ,
    uniformSpontaneousMagnetization_le_one d hJ hβ⟩

/-- **`uniformSpontaneousMagnetization² ≤ 1`** (ferromagnetic). -/
theorem uniformSpontaneousMagnetization_sq_le_one
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    uniformSpontaneousMagnetization d J β ^ 2 ≤ 1 :=
  spontaneousMagnetization_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **ℤ^d `-1 ≤ spontaneousMagnetization`** (ferromagnetic). -/
theorem neg_one_le_spontaneousMagnetization_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    -1 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  neg_one_le_spontaneousMagnetization (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d `|spontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    |spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i| ≤ 1 :=
  abs_spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≥ 0** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    0 ≤ spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i :=
  spontaneousMagnetization_nonneg (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d spontaneousMagnetization ≤ 1** (ferromagnetic). -/
theorem spontaneousMagnetization_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i ≤ 1 :=
  spontaneousMagnetization_le_one (IsingModel.latticeGraph d) Λ hJ hβ i

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

/-- **J-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ 0

/-- **h-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ 0

/-- **β-monotonicity of `uniformMagnetization` on ℤ^d**. -/
theorem uniformMagnetization_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => uniformMagnetization d ⟨J, h, β⟩)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh 0

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

/-- **`uniformMagnetization` at `J = h = 0`**:
`uniformMagnetization d ⟨0, 0, β⟩ = 0`.

At `J = h = 0` the Hamiltonian vanishes identically, so all site-level
correlations are zero. Direct from `correlationInfinite_zero_params_vanish`
at the singleton `{0}`. -/
theorem uniformMagnetization_zero_params
    (d : ℕ) (β : ℝ) :
    uniformMagnetization d (⟨0, 0, β⟩ : IsingParams ℝ) = 0 := by
  unfold uniformMagnetization magnetizationInfinite
  exact correlationInfinite_zero_params_vanish
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) β
    {(0 : Fin d → ℤ)} (by simp)

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

/-- **`-1 ≤ twoPointFunction`** unconditionally. Direct specialization
of `neg_one_le_correlationInfinite` at `A = {0, r}`. -/
theorem neg_one_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    -1 ≤ twoPointFunction d p r :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **ℤ^d `twoPointFunction ≥ tanh(β·h)²` for `r ≠ 0`** (ferromagnetic):
specialization of `correlationInfinite_ge_tanh_pow_card` at `A = {0, r}`
where `A.card = 2` (since `r ≠ 0`). -/
theorem twoPointFunction_ge_tanh_sq_of_ne
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * h) ^ 2 ≤ twoPointFunction d (⟨J, h, β⟩ : IsingParams ℝ) r := by
  have hcard : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair (Ne.symm hr)]
  have := correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ ({(0 : Fin d → ℤ), r} : Finset _)
  rw [hcard] at this
  exact this

/-- **`|twoPointFunction| ≤ 1`** unconditionally. Direct specialization
of `abs_correlationInfinite_le_one` at `A = {0, r}`. -/
theorem abs_twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    |twoPointFunction d p r| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction² ≤ 1`** unconditionally. Direct specialization
of `correlationInfinite_sq_le_one` at `A = {0, r}`. -/
theorem twoPointFunction_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction` at `h = 0, r = 0` vanishes** (Z₂ via
`twoPointFunction_zero` + `magnetizationInfinite_zero_at_h_zero`):
`twoPointFunction d ⟨J, 0, β⟩ 0 = 0`. -/
theorem twoPointFunction_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [twoPointFunction_zero,
      magnetizationInfinite_zero_at_h_zero]

/-- **`truncated2TwoPoint` at `h = 0, r = 0` vanishes**: at `r = 0`,
`truncated2TwoPoint = M · (1 − M)`; at `h = 0`, `M = 0` by Z₂, so the
product is `0`. -/
theorem truncated2TwoPoint_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [truncated2TwoPoint_zero,
      magnetizationInfinite_zero_at_h_zero]
  ring

/-- **J-monotonicity of `twoPointFunction`** (GJ Prop 4.2.1):
for `0 ≤ h, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`J` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_J` at
`A = {0, r}`. -/
theorem twoPointFunction_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun J : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_J d hh hβ
    {(0 : Fin d → ℤ), r}

/-- **h-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`h` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`. -/
theorem twoPointFunction_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun h : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_h d hJ hβ
    {(0 : Fin d → ℤ), r}

/-- **β-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 ≤ h`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`β` on `Ioi 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta`. -/
theorem twoPointFunction_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (r : Fin d → ℤ) :
    MonotoneOn (fun β : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ioi 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta d hJ hh
    {(0 : Fin d → ℤ), r}

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

/-- **Symmetry of `truncated4TwoPoint` under `(r, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r`. Derived by
chaining `_symm_rs`, `_symm_su`, `_symm_rs` to implement the transposition
`(r, u)` via adjacent swaps. -/
theorem truncated4TwoPoint_symm_ru
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r := by
  rw [truncated4TwoPoint_symm_rs d p r s u,
      truncated4TwoPoint_symm_su d p s r u,
      truncated4TwoPoint_symm_rs d p s u r]

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

/-- **`truncated2TwoPoint` at `J = h = 0` vanishes**:
`truncated2TwoPoint d ⟨0, 0, β⟩ r = 0`. All three Ursell terms vanish. -/
theorem truncated2TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated3TwoPoint` at `J = h = 0` vanishes**:
`truncated3TwoPoint d ⟨0, 0, β⟩ r s = 0`. All seven Ursell terms vanish. -/
theorem truncated3TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s = 0 := by
  unfold truncated3TwoPoint truncated3Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated4TwoPoint` at `J = h = 0` vanishes**:
`truncated4TwoPoint d ⟨0, 0, β⟩ r s u = 0`. All four Lebowitz terms vanish. -/
theorem truncated4TwoPoint_zero_params
    (d : ℕ) (β : ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d (⟨0, 0, β⟩ : IsingParams ℝ) r s u = 0 := by
  unfold truncated4TwoPoint truncated4Infinite
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r, s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {s, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), u} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ)
      {r, s} = 0 from
    correlationInfinite_zero_params_vanish _ _ β _ (by simp)]
  ring

/-- **`truncated2TwoPoint` at `β = 0` vanishes**:
`truncated2TwoPoint d ⟨J, h, 0⟩ r = 0`.

At infinite temperature `β = 0` all correlations vanish:
`correlationInfinite ... {0, r} = 0` (PR #278) and the magnetization
term is `0 · 0 = 0` (PR #276). Direct computation. -/
theorem truncated2TwoPoint_beta_zero
    (d : ℕ) (J h : ℝ) (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, h, 0⟩ : IsingParams ℝ) r = 0 := by
  unfold truncated2TwoPoint truncated2Infinite
  -- `correlationInfinite ... {0, r} = 0`, `correlationInfinite ... {0} = 0`,
  -- `correlationInfinite ... {r} = 0`.
  rw [show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ), r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {(0 : Fin d → ℤ)} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp),
      show correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, h, 0⟩ : IsingParams ℝ)
      {r} = 0 from
    correlationInfinite_beta_zero_vanish _ _ J h _ (by simp)]
  ring

/-- **`truncated2TwoPoint ≤ 1`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ 1`.

Upper bound: from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261), `twoPointFunction ≤ 1` (PR #260), and `M² ≥ 0`, we get
`truncated2TwoPoint ≤ 1 − 0 = 1`. -/
theorem truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ 1 := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_upper := twoPointFunction_le_one d p r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`-1 ≤ truncated2TwoPoint`** (ferromagnetic): from
`truncated2TwoPoint_nonneg`. -/
theorem neg_one_le_truncated2TwoPoint
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    -1 ≤ truncated2TwoPoint d p r := by
  have := truncated2TwoPoint_nonneg d p hf r
  linarith

/-- **`|truncated2TwoPoint| ≤ 1`** (ferromagnetic). -/
theorem abs_truncated2TwoPoint_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    |truncated2TwoPoint d p r| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_truncated2TwoPoint d p hf r,
    truncated2TwoPoint_le_one d p hf r⟩

/-- **`truncated2TwoPoint² ≤ 1`** (ferromagnetic). -/
theorem truncated2TwoPoint_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ^ 2 ≤ 1 := by
  have h := abs_truncated2TwoPoint_le_one d p hf r
  have : |truncated2TwoPoint d p r| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **`truncated2TwoPoint ≤ twoPointFunction`** on ℤ^d (ferromagnetic):
`truncated2TwoPoint d p r ≤ twoPointFunction d p r`.

Immediate from `truncated2TwoPoint = twoPointFunction − M²`
(PR #261) + `M² ≥ 0`: subtracting a nonneg quantity only decreases.
Physical content: the truncated 2-point function never exceeds the
connected 2-point function. -/
theorem truncated2TwoPoint_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    truncated2TwoPoint d p r ≤ twoPointFunction d p r := by
  have h_eq := truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
    d p hf r
  have h_sq : 0 ≤ (uniformMagnetization d p)^2 := sq_nonneg _
  linarith

/-- **`truncated2TwoPoint` at `h = 0` equals `twoPointFunction`** (ferromagnetic):
`truncated2TwoPoint d ⟨J, 0, β⟩ r = twoPointFunction d ⟨J, 0, β⟩ r`.

At zero external field `h = 0`, Z₂ symmetry forces `M = 0`
(`uniformMagnetization_zero_at_h_zero`), so
`truncated2TwoPoint = twoPointFunction − M² = twoPointFunction`. -/
theorem truncated2TwoPoint_h_zero_eq
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (r : Fin d → ℤ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) r
      = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      uniformMagnetization_zero_at_h_zero d J β]
  ring

/-- **`truncated2TwoPoint` at `J = 0` vanishes for `r ≠ 0`** (ferromagnetic):
`truncated2TwoPoint d ⟨0, h, β⟩ r = 0`.

At `J = 0` the Ising Hamiltonian has no coupling, so distinct sites are
independent. Consequently `⟨σ_0 σ_r⟩ = ⟨σ_0⟩⟨σ_r⟩ = M²`, and the
truncated 2-point function vanishes. Computation:
`truncated2TwoPoint = twoPointFunction − M² = tanh(βh)² − tanh(βh)² = 0`.
-/
theorem truncated2TwoPoint_J_zero_of_ne_zero
    (d : ℕ) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    truncated2TwoPoint d (⟨0, h, β⟩ : IsingParams ℝ) r = 0 := by
  rw [truncated2TwoPoint_eq_twoPointFunction_sub_uniformMagnetization_sq
        d _ hf r,
      twoPointFunction_J_zero_of_ne_zero d h β hf hr,
      uniformMagnetization_J_zero d h β hf]
  ring

/-- **ℤ^d spontaneousMagnetization exhaustion-independence**:
any two exhaustions yield the same `spontaneousMagnetization`. -/
theorem spontaneousMagnetization_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ' J β i :=
  spontaneousMagnetization_indep_exhaustion (IsingModel.latticeGraph d)
    Λ Λ' hJ hβ i

/-- **ℤ^d correlationInfinite at J = 0 general-A closed form** (ferromagnetic):
`correlationInfinite (latticeGraph d) Λ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf A

/-- **ℤ^d correlationInfinite at β = 0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_beta_zero_vanish (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d correlationInfinite at J=h=0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_zero_params_vanish (IsingModel.latticeGraph d) Λ β A hA

/-- **ℤ^d magnetizationInfinite ≤ 1** site-wise (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite ≥ 0** site-wise (any Exhaustion, ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    0 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d magnetizationInfinite J-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun J : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-- **ℤ^d magnetizationInfinite h-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    MonotoneOn
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  magnetizationInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationInfinite β-monotonicity** (any Exhaustion). -/
theorem magnetizationInfinite_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : Fin d → ℤ) :
    MonotoneOn
      (fun β : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  magnetizationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-- **ℤ^d correlationInfinite J-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ hh hβ A

/-- **ℤ^d correlationInfinite h-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **ℤ^d correlationInfinite β-monotonicity** (any Exhaustion). -/
theorem correlationInfinite_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh A

/-- **ℤ^d correlationAlongExhaustion J-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ A hJ₁ hJ₁₂ n

/-- **ℤ^d correlationAlongExhaustion h-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ A hh₁ hh₁₂ n

/-- **ℤ^d correlationAlongExhaustion β-monotonicity** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) A n
      ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) A n :=
  correlationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh A hβ₁ hβ₁₂ n

/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** site-wise (any Exhaustion, ferromagnetic):
combines `magnetizationInfinite_latticeGraph_nonneg` (so `0 ≤ M`, hence
`-1 ≤ M`) with `magnetizationInfinite_latticeGraph_le_one`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 := by
  have hl := magnetizationInfinite_latticeGraph_nonneg d Λ p hf i
  have hu := magnetizationInfinite_latticeGraph_le_one d Λ p i
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- **ℤ^d magnetizationΛ unfolding**: `magnetizationΛ G Λ p i = correlationΛ G Λ p {i}`. -/
theorem magnetizationΛ_latticeGraph_apply
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i
      = correlationΛ (IsingModel.latticeGraph d) Λ p {i} :=
  magnetizationΛ_apply (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationΛ ≤ 1** at any site `i : ↑Λ`. -/
theorem magnetizationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ p i ≤ 1 :=
  magnetizationΛ_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `|magnetizationΛ| ≤ 1`** at any site `i : ↑Λ`. -/
theorem abs_magnetizationΛ_latticeGraph_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    |magnetizationΛ (IsingModel.latticeGraph d) Λ p i| ≤ 1 :=
  abs_magnetizationΛ_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationΛ ≥ 0** for ferromagnetic `p` at any site `i : ↑Λ`. -/
theorem magnetizationΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : ↑Λ) :
    0 ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  magnetizationΛ_nonneg (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d magnetizationAlongExhaustion unfolding**:
`magnetizationAlongExhaustion G Λ p i n = correlationAlongExhaustion G Λ p {i} n`. -/
theorem magnetizationAlongExhaustion_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {i} n :=
  magnetizationAlongExhaustion_apply (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion `of_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      = correlationΛ (IsingModel.latticeGraph d) (Λ.volume n) p
          (liftFinset {i} (Finset.singleton_subset_iff.mpr hi)) :=
  magnetizationAlongExhaustion_of_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d magnetizationAlongExhaustion `of_not_mem` unfolding**. -/
theorem magnetizationAlongExhaustion_latticeGraph_of_not_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {i : Fin d → ℤ} {n : ℕ} (hi : i ∉ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n = 0 :=
  magnetizationAlongExhaustion_of_not_mem (IsingModel.latticeGraph d) Λ p hi

/-- **ℤ^d `magnetizationInfinite_apply`** unfolding. -/
theorem magnetizationInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = correlationInfinite (IsingModel.latticeGraph d) Λ p {i} :=
  magnetizationInfinite_apply (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `freeEnergyInfinite_apply`** unfolding (limsup form). -/
theorem freeEnergyInfinite_latticeGraph_apply
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      = Filter.limsup
          (freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p)
          Filter.atTop :=
  freeEnergyInfinite_apply (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d magnetizationAlongExhaustion ≤ 1** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n ≤ 1 :=
  magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationAlongExhaustion ≥ 0** per stage (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) (n : ℕ) :
    0 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationAlongExhaustion_nonneg (IsingModel.latticeGraph d) Λ p hf i n

/-- **ℤ^d magnetizationAlongExhaustion → magnetizationInfinite** (ferromagnetic):
Concrete specialization of `tendsto_magnetizationAlongExhaustion_magnetizationInfinite`. -/
theorem tendsto_magnetizationAlongExhaustion_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (magnetizationInfinite (IsingModel.latticeGraph d) Λ p i)) :=
  tendsto_magnetizationAlongExhaustion_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d existential convergence of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_convergent
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    ∃ L : ℝ, Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop (nhds L) :=
  magnetizationAlongExhaustion_convergent (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d stage-index monotonicity of `magnetizationAlongExhaustion`**
(ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Monotone (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i) :=
  magnetizationAlongExhaustion_monotone (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationAlongExhaustion` bounded above** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddAbove
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddAbove (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddAbove (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationAlongExhaustion` bounded below** (unconditional). -/
theorem correlationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    BddBelow (Set.range
      (correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A)) :=
  correlationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `magnetizationAlongExhaustion` bounded below** (unconditional). -/
theorem magnetizationAlongExhaustion_latticeGraph_bddBelow
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    BddBelow (Set.range
      (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)) :=
  magnetizationAlongExhaustion_bddBelow (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationAlongExhaustion → ⨆ n ...** (ferromagnetic). -/
theorem magnetizationAlongExhaustion_latticeGraph_tendsto_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    Filter.Tendsto
        (magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i)
      Filter.atTop
      (nhds (⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d)
        Λ p i n)) :=
  magnetizationAlongExhaustion_tendsto_ciSup (IsingModel.latticeGraph d) Λ p hf i

/-- **ℤ^d `magnetizationInfinite` as `ciSup`**:
`magnetizationInfinite = ⨆ n, magnetizationAlongExhaustion`. -/
theorem magnetizationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = ⨆ n, magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  magnetizationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `correlationInfinite` as `ciSup`**. -/
theorem correlationInfinite_latticeGraph_eq_ciSup
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      = ⨆ n, correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationInfinite_eq_ciSup (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion ≤ correlationInfinite`** pointwise. -/
theorem correlationAlongExhaustion_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  correlationAlongExhaustion_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `magnetizationAlongExhaustion ≤ magnetizationInfinite`** pointwise. -/
theorem magnetizationAlongExhaustion_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  magnetizationAlongExhaustion_le_magnetizationInfinite
    (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d magnetizationΛ h-monotonicity**: `MonotoneOn` in `h` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun h : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ i

/-- **ℤ^d magnetizationΛ β-monotonicity**: `MonotoneOn` in `β` on `Ioi 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (i : ↑Λ) :
    MonotoneOn
      (fun β : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ioi 0) :=
  magnetizationΛ_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh i

/-- **ℤ^d magnetizationΛ J-monotonicity**: `MonotoneOn` in `J` on `Ici 0`. -/
theorem magnetizationΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (i : ↑Λ) :
    MonotoneOn
      (fun J : ℝ => magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i)
      (Set.Ici 0) :=
  magnetizationΛ_monotone_J (IsingModel.latticeGraph d) Λ hh hβ i

/-- **ℤ^d magnetizationAlongExhaustion h-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ
    hJ hβ i hh₁ hh₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion β-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (i : Fin d → ℤ) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ
    hJ hh i hβ₁ hβ₁₂ n

/-- **ℤ^d magnetizationAlongExhaustion J-monotonicity** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (i : Fin d → ℤ) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) i n
      ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ
    hh hβ i hJ₁ hJ₁₂ n

/-- **ℤ^d magnetizationΛ at h = 0 vanishes (Z₂)**. -/
theorem magnetizationΛ_latticeGraph_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationAlongExhaustion at h = 0 vanishes (Z₂)** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_h_zero (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d magnetizationΛ vanishes at β=0**. -/
theorem magnetizationΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at β=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_beta_zero (IsingModel.latticeGraph d) Λ J h i n

/-- **ℤ^d magnetizationΛ vanishes at J=h=0**. -/
theorem magnetizationΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_zero_params (IsingModel.latticeGraph d) Λ β i

/-- **ℤ^d magnetizationAlongExhaustion vanishes at J=h=0** per stage. -/
theorem magnetizationAlongExhaustion_latticeGraph_zero_params
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  magnetizationAlongExhaustion_zero_params (IsingModel.latticeGraph d) Λ β i n

/-- **ℤ^d magnetizationΛ at J=0 closed form**: `= tanh(β·h)`. -/
theorem magnetizationΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  magnetizationΛ_J_zero (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d magnetizationAlongExhaustion at J=0** per stage (on-stage):
`i ∈ Λ.volume n ⇒ = tanh(β·h)`. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_of_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    {i : Fin d → ℤ} {n : ℕ} (hi : i ∈ Λ.volume n) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_of_mem (IsingModel.latticeGraph d) Λ h β hi

/-- **ℤ^d magnetizationAlongExhaustion at J=0 is eventually `tanh(β·h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_J_zero_eventually_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (i : Fin d → ℤ) :
    ∀ᶠ n in Filter.atTop,
      magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) i n = Real.tanh (β * h) :=
  magnetizationAlongExhaustion_J_zero_eventually_eq
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d pointwise `|correlationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_correlationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    |correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n| ≤ 1 :=
  abs_correlationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d pointwise `|magnetizationAlongExhaustion| ≤ 1`** at every `n`. -/
theorem abs_magnetizationAlongExhaustion_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n| ≤ 1 :=
  abs_magnetizationAlongExhaustion_le_one (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `|correlationInfinite| ≤ 1`** (unconditional). -/
theorem abs_correlationInfinite_latticeGraph_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    |correlationInfinite (IsingModel.latticeGraph d) Λ p A| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `|magnetizationInfinite| ≤ 1`** (unconditional). -/
theorem abs_magnetizationInfinite_latticeGraph_le_one_unconditional
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ p i| ≤ 1 :=
  abs_magnetizationInfinite_le_one (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `-1 ≤ correlationΛ`**. -/
theorem neg_one_le_correlationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationΛ (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `-1 ≤ correlationAlongExhaustion`** per stage. -/
theorem neg_one_le_correlationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    -1 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  neg_one_le_correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `-1 ≤ correlationInfinite`** (unconditional). -/
theorem neg_one_le_correlationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    -1 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p A :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationΛ² ≤ 1`**. -/
theorem correlationΛ_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationΛ_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `correlationAlongExhaustion² ≤ 1`** per stage. -/
theorem correlationAlongExhaustion_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n ^ 2 ≤ 1 :=
  correlationAlongExhaustion_sq_le_one (IsingModel.latticeGraph d) Λ p A n

/-- **ℤ^d `correlationInfinite² ≤ 1`**. -/
theorem correlationInfinite_latticeGraph_sq_le_one
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d) Λ p A

/-- **ℤ^d `-1 ≤ magnetizationΛ`**. -/
theorem neg_one_le_magnetizationΛ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (i : ↑Λ) :
    -1 ≤ magnetizationΛ (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationΛ (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d `-1 ≤ magnetizationAlongExhaustion`** per stage. -/
theorem neg_one_le_magnetizationAlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) (n : ℕ) :
    -1 ≤ magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n :=
  neg_one_le_magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ p i n

/-- **ℤ^d `-1 ≤ magnetizationInfinite`** (unconditional). -/
theorem neg_one_le_magnetizationInfinite_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ) :
    -1 ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ p i :=
  neg_one_le_magnetizationInfinite (IsingModel.latticeGraph d) Λ p i

/-- **ℤ^d magnetizationInfinite at h = 0 site-wise**:
`magnetizationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i = 0`. -/
theorem magnetizationInfinite_latticeGraph_zero_at_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i = 0 :=
  magnetizationInfinite_zero_at_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationInfinite at β = 0 site-wise**. -/
theorem magnetizationInfinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, 0⟩ i = 0 :=
  magnetizationInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationInfinite at J = 0 site-wise** (ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i
      = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf i

/-- **ℤ^d magnetizationInfinite exhaustion-independence**:
any two exhaustions of `Fin d → ℤ` yield the same ∞-vol magnetization. -/
theorem magnetizationInfinite_latticeGraph_indep_exhaustion
    (d : ℕ) (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ p i
      = magnetizationInfinite (IsingModel.latticeGraph d) Λ' p i :=
  magnetizationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i

/-- **ℤ^d empty-set correlation is 1**: `correlationInfinite ... p ∅ = 1`.
Gibbs-measure normalisation — an empty spin product is `1`. -/
@[simp]
theorem correlationInfinite_latticeGraph_cubicExhaustion_empty
    (d : ℕ) (p : IsingParams ℝ) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p ∅ = 1 :=
  correlationInfinite_empty (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p

/-- **ℤ^d FKG for spinProducts at ∞-vol** (Glimm–Jaffe §4.4 p. 67):
alias of the `correlationInfinite_gks_second` GKS-II form. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_fkg_spinProduct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A
      * correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p B
      ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (A ∆ B) :=
  correlationInfinite_fkg_spinProduct (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A B

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationΛ`**:
odd-cardinality spin product vanishes at h=0. -/
theorem correlationΛ_latticeGraph_odd_vanish_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    correlationΛ (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ A = 0 :=
  correlationΛ_odd_vanish_h_zero (IsingModel.latticeGraph d) Λ J β A hodd

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationAlongExhaustion`** stage-wise. -/
theorem correlationAlongExhaustion_latticeGraph_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A n = 0 :=
  correlationAlongExhaustion_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd n

/-- **ℤ^d Z₂ symmetry at `h = 0` for `correlationInfinite`**:
`correlationInfinite ⟨J, 0, β⟩ A = 0` for any `A` of odd cardinality. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_h_zero
    (d : ℕ) (J β : ℝ) (A : Finset (Fin d → ℤ)) (hodd : Odd A.card) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ A = 0 :=
  correlationInfinite_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β A hodd

/-- **ℤ^d Cor 4.3.5 at ∞-volume** (Glimm–Jaffe §4.3 Cor 4.3.5 p. 62):
inductive (n+2)-point bound at `h = 0` on ℤ^d. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_cor_4_3_5_h0
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (Fin d → ℤ)) {j k : Fin d → ℤ}
    (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j (insert k S))
      ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ S *
          correlationInfinite (IsingModel.latticeGraph d)
            (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ {j, k} +
        ∑ T ∈ S.powerset,
          correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert j T) *
            correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) ⟨J, 0, β⟩ (insert k (S \ T)) :=
  correlationInfinite_cor_4_3_5_h0 (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf S hj hk hjk

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
