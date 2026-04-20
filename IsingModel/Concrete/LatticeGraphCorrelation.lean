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

end Ambient

end IsingModel
