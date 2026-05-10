/- Translation.lean
Concrete translation invariance theorems for the ℤ^d Ising model:
finite-volume, along-exhaustion, and infinite-volume wrappers for
correlations, partition functions, free energy, truncated 2/3/4-point
functions, and spontaneous correlation/magnetization.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice

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

/-! ## Any-exhaustion and finite-volume translation wrappers -/

/-- **ℤ^d correlationInfinite translation invariance** (any-Exhaustion):
`correlationInfinite p (vaddFinset t A) = correlationInfinite p A`. -/
theorem correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p (vaddFinset t A)
      = correlationInfinite (IsingModel.latticeGraph d) Λ p A := by
  classical
  exact correlationInfinite_vaddFinset_of_translationInvariant
    (IsingModel.latticeGraph d) Λ t p hf A

/-- **ℤ^d spontaneousCorrelation translation invariance** (any-Exhaustion):
for ferromagnetic `(J ≥ 0, β > 0)`,
`spontaneousCorrelation J β (vaddFinset t A) = spontaneousCorrelation J β A`. -/
theorem spontaneousCorrelation_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β (vaddFinset t A)
      = spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A := by
  classical
  exact spontaneousCorrelation_translation
    (IsingModel.latticeGraph d) Λ t hJ hβ A

/-- **ℤ^d spontaneousMagnetization translation invariance** (any-Exhaustion):
for ferromagnetic `(J ≥ 0, β > 0)`,
`spontaneousMagnetization J β (t +ᵥ i) = spontaneousMagnetization J β i`. -/
theorem spontaneousMagnetization_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β (t +ᵥ i)
      = spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i := by
  classical
  exact spontaneousMagnetization_translation
    (IsingModel.latticeGraph d) Λ t hJ hβ i

/-- **ℤ^d truncated2Infinite translation invariance** (any-Exhaustion):
`U_2(t+i, t+j) = U_2(i, j)`. -/
theorem truncated2Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : Fin d → ℤ) :
    truncated2Infinite (IsingModel.latticeGraph d) Λ p (t +ᵥ i) (t +ᵥ j)
      = truncated2Infinite (IsingModel.latticeGraph d) Λ p i j := by
  classical
  exact truncated2Infinite_translation (IsingModel.latticeGraph d) Λ t p hf i j

/-- **ℤ^d truncated3Infinite translation invariance** (any-Exhaustion):
`U_3(t+i, t+j, t+k) = U_3(i, j, k)`. -/
theorem truncated3Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ p
        (t +ᵥ i) (t +ᵥ j) (t +ᵥ k)
      = truncated3Infinite (IsingModel.latticeGraph d) Λ p i j k := by
  classical
  exact truncated3Infinite_translation (IsingModel.latticeGraph d) Λ t p hf i j k

/-- **ℤ^d truncated4Infinite translation invariance** (any-Exhaustion):
`U_4(t+i, t+j, t+k, t+l) = U_4(i, j, k, l)`. -/
theorem truncated4Infinite_latticeGraph_translation
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ p
        (t +ᵥ i) (t +ᵥ j) (t +ᵥ k) (t +ᵥ l)
      = truncated4Infinite (IsingModel.latticeGraph d) Λ p i j k l := by
  classical
  exact truncated4Infinite_translation
    (IsingModel.latticeGraph d) Λ t p hf i j k l

/-- **ℤ^d freeEnergyAlongExhaustion shift translation invariance**:
`freeEnergyAlongExhaustion (Λ.shift t) n = freeEnergyAlongExhaustion Λ n`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_shift_eq (IsingModel.latticeGraph d) Λ t p n

/-- **ℤ^d freeEnergyInfinite shift translation invariance**:
`freeEnergyInfinite (Λ.shift t) = freeEnergyInfinite Λ`. -/
theorem freeEnergyInfinite_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) (Λ.shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d) Λ t p

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

/-- **ℤ^d correlationAlongExhaustion shift translation invariance**:
`correlationAlongExhaustion (Λ.shift t) (vaddFinset t A) n = correlationAlongExhaustion Λ A n`. -/
theorem correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p
        (vaddFinset t A) n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_shift_vaddFinset_eq
    (IsingModel.latticeGraph d) Λ t p A n

/-- **ℤ^d correlationΛ translation invariance**:
`⟨σ^{vadd A}⟩_{t +ᵥ Λ}(p) = ⟨σ^A⟩_Λ(p)` on ℤ^d. -/
theorem correlationΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p A

/-- **ℤ^d partitionFunctionΛ translation invariance**:
`Z_{t +ᵥ Λ}(p) = Z_Λ(p)` on ℤ^d. -/
theorem partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d freeEnergyΛ translation invariance**:
`f_{t +ᵥ Λ}(p) = f_Λ(p)` on ℤ^d. -/
theorem freeEnergyΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d log_partitionFunctionΛ translation invariance**:
`log Z_{t +ᵥ Λ}(p) = log Z_Λ(p)` on ℤ^d. -/
theorem log_partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        (vaddFinset t Λ) p)
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) := by
  rw [partitionFunctionΛ_latticeGraph_vaddFinset_eq d t Λ p]

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

/-- **Right-limit** `correlationInfinite ⟨J, h, β⟩ → spontaneousCorrelation J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation (IsingModel.latticeGraph d) Λ J β A)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ A

/-- **Right-limit** `magnetizationInfinite ⟨J, h, β⟩ → spontaneousMagnetization J β`
as `h → 0⁺` on ℤ^d (any-Exhaustion). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_latticeGraph_any
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : Fin d → ℤ) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite (IsingModel.latticeGraph d) Λ
        ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization (IsingModel.latticeGraph d) Λ J β i)) :=
  tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (IsingModel.latticeGraph d) Λ hJ hβ i

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

/-- **Site-independence of ℤ^d spontaneous magnetization**: for `0 ≤ J`,
`0 < β`, and any two sites `i j : Fin d → ℤ`,
`spontaneousMagnetization (latticeGraph d) (cubicExhaustion d) J β i
  = spontaneousMagnetization (latticeGraph d) (cubicExhaustion d) J β j`.

Proof: set `t := j - i`; `spontaneousMagnetization_translation` gives
`... (t +ᵥ i) = ... i`, and `t +ᵥ i = j` on ℤ^d by `abel`. -/
theorem spontaneousMagnetization_latticeGraph_cubicExhaustion_eq
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i j : Fin d → ℤ) :
    spontaneousMagnetization (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β i
      = spontaneousMagnetization (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β j := by
  have h := spontaneousMagnetization_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) (j - i) hJ hβ i
  have hvadd : (j - i) +ᵥ i = j := by
    change (j - i) + i = j
    abel
  rw [hvadd] at h
  exact h.symm

end Ambient
end IsingModel
