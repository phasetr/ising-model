import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfiniteMonotoneCubicEx
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# ℤ^d twoPointFunction monotone wrappers

Narrow child module for three ℤ^d
`twoPointFunction_monotone_{J,h,beta}` wrappers (GJ Prop 4.2.1). Each
wrapper is a thin pass-through to the corresponding ambient
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_*` lemma at
`A = {(0 : Fin d → ℤ), r}`.
-/

namespace IsingModel
namespace Ambient

/-- **J-monotonicity of `twoPointFunction`** (GJ Prop 4.2.1):
for `0 ≤ h, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`J` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_J` at
`A = {0, r}`. -/
theorem twoPointFunction_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun J : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_J d hh hβ
    {(0 : Fin d → ℤ), r}

/-- **h-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`h` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`. -/
theorem twoPointFunction_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun h : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_h d hJ hβ
    {(0 : Fin d → ℤ), r}

/-- **β-monotonicity of `twoPointFunction`** (GJ Prop 4.2.4):
for `0 ≤ J, 0 ≤ h`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`β` on `Ioi 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta`. -/
theorem twoPointFunction_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (r : Fin d → ℤ) :
    MonotoneOn (fun β : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ioi 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_beta d hJ hh
    {(0 : Fin d → ℤ), r}

end Ambient
end IsingModel
