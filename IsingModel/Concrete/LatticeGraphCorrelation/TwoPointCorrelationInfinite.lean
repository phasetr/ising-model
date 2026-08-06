/- TwoPointCorrelationInfinite.lean
Narrow child module for the 7 ℤ^d `correlationInfinite_latticeGraph_*`
wrappers (`_le_one`, `_nonneg`, `_indep_exhaustion`,
`_cubicExhaustion_monotone_h`, `_beta`, `_J`, `_gks_second`)
extracted from `TwoPoint.lean` in PR #2025. The theorem names are
unchanged from the former `TwoPoint` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

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

/-! ## Moved: cubicExhaustion monotone wrappers

The three wrappers
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`,
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta`,
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_J` now
live in `TwoPointCorrelationInfiniteMonotoneCubicEx.lean`. -/


/-- **GKS-II at ∞-volume on ℤ^d**: for ferromagnetic `p` and any
`A, B : Finset (Fin d → ℤ)`,

`correlationInfinite ... p A · correlationInfinite ... p B
  ≤ correlationInfinite ... p (A ∆ B)`.

Concrete ℤ^d specialisation of `correlationInfinite_gks_second`
(Glimm–Jaffe §4.2 Thm 4.2.3). -/
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
