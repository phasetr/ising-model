import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlation trivial / GKS-II / FKG / h_zero / cor 4.3.5 wrappers

Narrow child module for 15 ℤ^d wrappers covering:

- `magnetizationInfinite_latticeGraph_*` trivial slices
  (`zero_at_h_zero`, `beta_zero`, `J_zero`, `indep_exhaustion`);
- `correlationInfinite_latticeGraph_cubicExhaustion_empty`;
- `correlationInfinite_latticeGraph_gks_second` /
  `_fkg_spinProduct` / `_cubicExhaustion_fkg_spinProduct`;
- `correlationΛ_latticeGraph_odd_vanish_h_zero`;
- `correlationAlongExhaustion_latticeGraph_h_zero` /
  `_any_h_zero`;
- `correlationInfinite_latticeGraph_cubicExhaustion_h_zero` /
  `_h_zero`;
- `correlationInfinite_latticeGraph_cor_4_3_5_h0` /
  `_cubicExhaustion_cor_4_3_5_h0`.

Theorem names are unchanged from the former `UniformMag`
declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Moved: magnetizationInfinite trivial-slice wrappers

The three wrappers
`magnetizationInfinite_latticeGraph_zero_at_h_zero`,
`magnetizationInfinite_latticeGraph_beta_zero`,
`magnetizationInfinite_latticeGraph_J_zero` now live in
`UniformMagCorrelationTrivialTrivialSlices.lean`. -/


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

/-- **ℤ^d FKG for spinProducts at ∞-vol** (Glimm–Jaffe §4.4 p. 67):
alias of the `correlationInfinite_gks_second` GKS-II form. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_fkg_spinProduct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A
      * correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p B
      ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p (A ∆ B) :=
  correlationInfinite_fkg_spinProduct (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A B

/-! ## Moved: correlation h_zero (Z₂ symmetry) wrappers

The five wrappers `correlationΛ_latticeGraph_odd_vanish_h_zero`,
`correlationAlongExhaustion_latticeGraph_h_zero`,
`correlationInfinite_latticeGraph_cubicExhaustion_h_zero`,
`correlationInfinite_latticeGraph_h_zero`, and
`correlationAlongExhaustion_latticeGraph_any_h_zero` now live in
`UniformMagCorrelationTrivialHZero.lean`. -/

/-! ## Moved: Cor 4.3.5 ∞-volume correlation wrappers

The two `correlationInfinite_latticeGraph_*_cor_4_3_5_h0` wrappers
now live in `UniformMagCorrelationTrivialCor4_3_5.lean`. -/



/-! ## Moved: susceptibility / magnetizationInfinite J_zero regularity wrappers

The 11 ℤ^d `susceptibilityInfinite_latticeGraph_*` and
`magnetizationInfinite_latticeGraph_*` J_zero / β_zero /
zero_params trivial-slice + continuousOn / differentiableOn
regularity wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.UniformMagSusceptibilityInfinite`.
The earlier import path is preserved by re-importing the new child.
-/

end Ambient

end IsingModel
