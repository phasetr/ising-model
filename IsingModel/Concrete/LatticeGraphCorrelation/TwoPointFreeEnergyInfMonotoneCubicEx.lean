import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_*` wrappers

Narrow child module for three ℤ^d
`freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_*` wrappers
extracted from `TwoPointFreeEnergyInfMonotone.lean`:

* `freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_J`,
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_h`,
* `freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_beta`.

Each result instantiates the corresponding generic
`freeEnergyInfinite_monotone_*` lemma at the concrete cubic
exhaustion via the BED constant `c = d`. The theorem names are
unchanged from the former `TwoPointFreeEnergyInfMonotone`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **J-monotonicity of `freeEnergyInfinite` on ℤ^d** under the concrete
BED constant `c = d` (PR #246). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **β-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  refine freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)


end Ambient

end IsingModel
