import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfiniteMonotoneCubicEx
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# Parameter monotonicity of the ℤ^d two-point function

Concrete statements about `twoPointFunction` at `IsingModel.latticeGraph d` along
`Ambient.cubicExhaustion d`, at an arbitrary separation. The value is monotone in the
coupling on `Set.Ici 0` assuming a non-negative external field and a positive inverse
temperature, in the external field on `Set.Ici 0` assuming a non-negative coupling and a
positive inverse temperature, and in the inverse temperature on `Set.Ioi 0` assuming a
non-negative coupling and a non-negative external field. Each is the corresponding
monotonicity of `correlationInfinite` read at the anchoring site set. No instance argument
is taken.

The mathematical source is Glimm-Jaffe, *Quantum Physics*, Proposition 4.2.1, p. 58: a
correlation function is monotone increasing in the couplings of the Hamiltonian. Raising
the external field raises the singleton couplings, which is the remark Glimm-Jaffe make on
that same page; raising the inverse temperature at a non-negative coupling and a
non-negative field raises every coupling at once.
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

/-- **h-monotonicity of `twoPointFunction`** (GJ Prop 4.2.1, p. 58, at the singleton
couplings):
for `0 ≤ J, 0 < β`, `twoPointFunction d ⟨J, h, β⟩ r` is monotone in
`h` on `Ici 0`. Direct specialization of
`correlationInfinite_latticeGraph_cubicExhaustion_monotone_h`. -/
theorem twoPointFunction_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (r : Fin d → ℤ) :
    MonotoneOn (fun h : ℝ => twoPointFunction d ⟨J, h, β⟩ r) (Set.Ici 0) :=
  correlationInfinite_latticeGraph_cubicExhaustion_monotone_h d hJ hβ
    {(0 : Fin d → ℤ), r}

/-- **β-monotonicity of `twoPointFunction`** (GJ Prop 4.2.1, p. 58, at all couplings at
once):
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
