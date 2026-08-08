import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d infinite-volume translation-invariance wrappers

Instantiates translation invariance of the infinite-volume observables at
`IsingModel.latticeGraph d` — the correlation under a shifted finset, the magnetization, and
the spontaneous quantities — which is what makes the ℤ^d limit state translation invariant.
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

end Ambient

end IsingModel
