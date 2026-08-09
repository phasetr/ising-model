import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Sign of the ℤ^d truncated two-point correlation, and its comparison with the untruncated

Concrete `IsingModel.latticeGraph d` statements, all assuming `Ferromagnetic` on the
parameter record.

Along `Ambient.cubicExhaustion d` the truncated two-point correlation is non-negative. That
is recorded at an arbitrary pair of sites, again at a pair carrying an explicit distinctness
hypothesis, and on the diagonal, where the sites are one and the same variable rather than
the subject of a hypothesis. Along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` the
truncated correlation is at most the untruncated infinite-volume correlation of the pair.

That distinctness hypothesis is the only assumption anywhere here beyond `Ferromagnetic`,
and no instance argument is taken.
-/

namespace IsingModel
namespace Ambient


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

end Ambient

end IsingModel
