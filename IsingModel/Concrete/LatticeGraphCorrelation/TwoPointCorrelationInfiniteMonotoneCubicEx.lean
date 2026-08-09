import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Parameter monotonicity of the ℤ^d infinite-volume correlation

Concrete `IsingModel.latticeGraph d` statements along `Ambient.cubicExhaustion d`, at a
fixed finite site set. The correlation is monotone in the external field on `Set.Ici 0`
assuming a non-negative coupling and a positive inverse temperature, in the inverse
temperature on `Set.Ioi 0` assuming a non-negative coupling and a non-negative external
field, and in the coupling on `Set.Ici 0` assuming a non-negative external field and a
positive inverse temperature. No instance argument is taken.

## References

* Glimm-Jaffe, *Quantum Physics*, Proposition 4.2.1, p. 58: a correlation function is
  monotone increasing in the couplings of the Hamiltonian. Raising the external field
  raises the singleton couplings, the remark Glimm-Jaffe make on that same page; raising
  the inverse temperature at a non-negative coupling and a non-negative field raises every
  coupling at once.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **h-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.1, p. 58, at the
singleton couplings):
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

/-- **β-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.1, p. 58, at all
couplings at once):
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

/-- **J-monotonicity of correlationInfinite on ℤ^d** (GJ Prop 4.2.1, p. 58):
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
