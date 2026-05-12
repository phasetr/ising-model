/- TranslationVadd.lean
Narrow child module for the 11 ℤ^d translation invariance wrappers
(`correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`,
4 `*_latticeGraph_cubicExhaustion_translation` for `magnetizationInfinite`
and `truncated{2,3,4}Infinite`,
`correlationInfinite_latticeGraph_vaddFinset_of_translationInvariant`,
and 5 `*_latticeGraph_translation` for `spontaneousCorrelation`,
`spontaneousMagnetization`, and `truncated{2,3,4}Infinite`) extracted
from `Translation.lean` in PR #2061. Each is a thin pass-through to
the corresponding abstract translation-invariance lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from the
former `Translation` declarations.
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


end Ambient

end IsingModel
