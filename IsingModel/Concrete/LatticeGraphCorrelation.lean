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
  have h_singleton : ({t +ᵥ i} : Finset (Fin d → ℤ)) = vaddFinset t {i} := by
    ext x
    rw [mem_vaddFinset, Finset.mem_singleton]
    constructor
    · intro heq; exact ⟨i, Finset.mem_singleton_self i, heq.symm⟩
    · rintro ⟨u, huA, heq⟩
      rw [Finset.mem_singleton] at huA
      subst huA
      exact heq.symm
  rw [h_singleton]
  exact correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d t p hf {i}

end Ambient

end IsingModel
