import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Range, exhaustion-independence and GKS-II for the ℤ^d infinite-volume correlation

Concrete `IsingModel.latticeGraph d` statements about `correlationInfinite` at a finite
site set.

Along an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` the value is at most `1`, with no
assumption on the parameter record. Under `Ferromagnetic` it is also non-negative, and it
does not depend on which exhaustion computes it — the exhaustion-independence corollary of
the infinite-volume convergence theorem of Glimm-Jaffe, *Quantum Physics*, Theorem 4.2.3,
p. 59. Along `Ambient.cubicExhaustion d`, and again under `Ferromagnetic`, the product of
the values at two site sets is at most the value at their symmetric difference. No instance
argument is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient


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

/-- **GKS-II at ∞-volume on ℤ^d**: for ferromagnetic `p` and any
`A, B : Finset (Fin d → ℤ)`,

`correlationInfinite ... p A · correlationInfinite ... p B
  ≤ correlationInfinite ... p (A ∆ B)`.

Concrete ℤ^d specialisation of `correlationInfinite_gks_second`
(Glimm–Jaffe §4.1 Thm 4.1.3, p. 57, in its Ising symmetric-difference form). -/
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


end Ambient

end IsingModel
