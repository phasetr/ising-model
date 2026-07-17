import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `correlationInfinite_latticeGraph_cubicExhaustion_monotone_*` wrappers

Narrow child module for three ℤ^d
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_*` wrappers
extracted from `TwoPointCorrelationInfinite.lean`:

* `correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`,
* `correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta`,
* `correlationInfinite_latticeGraph_cubicExhaustion_monotone_J`.

Each result is a thin pass-through of the ambient
`Ambient.correlationInfinite_monotone_*` lemma at
`G := IsingModel.latticeGraph d` and the concrete `cubicExhaustion d`.
The theorem names are unchanged from the former
`TwoPointCorrelationInfinite` declarations.

## References

* Glimm–Jaffe §4.2 Prop 4.2.1, Prop 4.2.4.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **h-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.4):
for `0 ≤ J, 0 < β`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`h ∈ Ici 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun h : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ A

/-- **β-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.4):
for `0 ≤ J, 0 ≤ h`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`β ∈ Ioi 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ioi 0) :=
  correlationInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh A

/-- **J-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.1):
for `0 ≤ h, 0 < β`, `correlationInfinite ⟨J, h, β⟩ A` is monotone on
`J ∈ Ici 0`. -/
theorem correlationInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ A)
      (Set.Ici 0) :=
  correlationInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ A

end Ambient

end IsingModel
