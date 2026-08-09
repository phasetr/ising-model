import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationVadd

/-!
# ℤ^d independence of the exhaustion and of the site

Concrete `latticeGraph d` statements that certain infinite-volume quantities do not depend on
choices made in their construction. For a fixed finite subset of `Fin d → ℤ`, and under
`0 ≤ J` and `0 < β`, the spontaneous correlation agrees along any pair of
`Ambient.Exhaustion`s of `Fin d → ℤ`. At `Ambient.cubicExhaustion d` the infinite-volume
magnetization agrees at any pair of sites for a parameter record satisfying `Ferromagnetic`,
and the spontaneous magnetization agrees at any pair of sites under `0 ≤ J` and `0 < β`; each
is read off translation invariance by translating one site onto the other. No instance
argument is taken.
-/

namespace IsingModel
namespace Ambient

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
