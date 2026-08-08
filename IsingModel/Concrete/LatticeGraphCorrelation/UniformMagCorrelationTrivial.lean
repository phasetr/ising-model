import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d infinite-volume correlation GKS-II / FKG and trivial-case wrappers

Instantiates the GKS-II and FKG correlation inequalities for the ℤ^d infinite-volume state,
together with the degenerate empty-subset value and the independence of the infinite-volume
magnetization from the chosen exhaustion.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

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

/-- **ℤ^d GKS-II at ∞-vol** (any-Exhaustion): for ferromagnetic `p`,
`⟨σ^A⟩·⟨σ^B⟩ ≤ ⟨σ^{A ∆ B}⟩` at ∞-volume. -/
theorem correlationInfinite_latticeGraph_gks_second
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      * correlationInfinite (IsingModel.latticeGraph d) Λ p B
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p (A ∆ B) :=
  correlationInfinite_gks_second (IsingModel.latticeGraph d) Λ p hf A B

/-- **ℤ^d FKG for spinProducts at ∞-vol** (any-Exhaustion): alias of
GKS-II form. -/
theorem correlationInfinite_latticeGraph_fkg_spinProduct
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p A
      * correlationInfinite (IsingModel.latticeGraph d) Λ p B
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p (A ∆ B) :=
  correlationInfinite_fkg_spinProduct (IsingModel.latticeGraph d) Λ p hf A B

end Ambient

end IsingModel
