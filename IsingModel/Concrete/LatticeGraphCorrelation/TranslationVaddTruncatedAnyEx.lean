import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated{2,3,4}Infinite translation invariance wrappers

Narrow child module for three ℤ^d
`truncated{2,3,4}Infinite_latticeGraph_translation` (any-Exhaustion)
wrappers extracted from `TranslationVadd.lean`. Each wrapper is a thin
pass-through to the corresponding ambient
`truncated{2,3,4}Infinite_translation` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

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
