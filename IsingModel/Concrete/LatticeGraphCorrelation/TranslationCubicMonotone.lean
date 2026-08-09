import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d translation invariance and parameter monotonicity of the spontaneous correlation

Concrete `latticeGraph d` statements at `Ambient.cubicExhaustion d`, for a fixed finite
subset of `Fin d → ℤ`. Translating the subset by a lattice vector leaves the spontaneous
correlation unchanged, under `0 ≤ J` and `0 < β`. As a function of the coupling it is
monotone on `Set.Ici 0`, assuming only `0 < β`; as a function of the inverse temperature it
is monotone on `Set.Ioi 0`, assuming only `0 ≤ J`. No instance argument is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Translation invariance of `spontaneousCorrelation` on ℤ^d**:
for `0 ≤ J`, `0 < β` and any `t : Fin d → ℤ`,
`spontaneousCorrelation ... J β (vaddFinset t A) = spontaneousCorrelation ... J β A`. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_translation
    (d : ℕ) (t : Fin d → ℤ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    (A : Finset (Fin d → ℤ)) :
    spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β (vaddFinset t A)
      = spontaneousCorrelation (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) J β A :=
  spontaneousCorrelation_translation (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t hJ hβ A

/-- **J-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {β : ℝ} (hβ : 0 < β) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun J : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ici 0) :=
  spontaneousCorrelation_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hβ A

/-- **β-monotonicity of `spontaneousCorrelation` on ℤ^d**. -/
theorem spontaneousCorrelation_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) (A : Finset (Fin d → ℤ)) :
    MonotoneOn
      (fun β : ℝ => spontaneousCorrelation (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) J β A)
      (Set.Ioi 0) :=
  spontaneousCorrelation_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ A


end Ambient
end IsingModel
