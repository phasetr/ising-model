import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete freeEnergyInfinite high-temperature wrappers

Narrow child module for the §18.3-§18.4 concrete `freeEnergyInfinite`
high-temperature wrappers on `latticeGraph d` (with caller-supplied
`Exhaustion` BED witness) and on `cubicExhaustion d` (with the BED
constant `c = d`). 10 theorems: `upper_bound_exp_uniform`,
`upper_bound_exp`, `sandwich_exp`, `complete_summary_exp`,
`deviation_bound_exp`, `continuity_at_J_zero`,
`continuity_at_beta_zero`, `continuity_bundle`,
`deviation_sandwich_exp`, `ratio_bound_bundle`. The theorem names are
unchanged from the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d ∞-vol sharper f upper bound via caller-supplied BED**:
under ferromagnetic `0 ≤ J, 0 < β` + bounded-edge-density witness `c`
on any `Exhaustion`, `freeEnergyInfinite ⟨J, 0, β⟩ ≤ log 2 + β·J·c`.
ℤ^d wrapper of `freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform`. -/
theorem freeEnergyInfinite_latticeGraph_high_temp_h_zero_upper_bound_exp_uniform
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * c :=
  freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    (IsingModel.latticeGraph d) Λ J β hJ hβ hc

/-- **ℤ^d ∞-vol sharper f upper bound on `cubicExhaustion d`**: under
ferromagnetic `0 ≤ J, 0 < β`,
`freeEnergyInfinite ⟨J, 0, β⟩ ≤ log 2 + β·J·d`. ℤ^d-cubic
specialization (constant `c = d` via `inducedLatticeGraph_card_edgeFinset_le`). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_upper_bound_exp
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_upper_bound_exp_uniform
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d ∞-vol sharper f sandwich on `cubicExhaustion d`**: under
ferromagnetic `0 ≤ J, 0 < β`,
`log 2 ≤ freeEnergyInfinite ⟨J, 0, β⟩ ≤ log 2 + β·J·d`. ℤ^d wrapper of
`freeEnergyInfinite_high_temp_h_zero_sandwich_exp_uniform`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_sandwich_exp
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_sandwich_exp_uniform
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d ∞-vol f complete-summary on `cubicExhaustion d`**: under
ferromagnetic `0 ≤ J, 0 < β`, single statement bundling sandwich
bounds and trivial-slice values at the ℤ^d concrete level.
ℤ^d wrapper of `freeEnergyInfinite_high_temp_h_zero_complete_summary_exp`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_complete_summary_exp
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2 + β * J * (d : ℝ) ∧
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  refine freeEnergyInfinite_high_temp_h_zero_complete_summary_exp
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d ∞-vol f deviation bound on cubicExhaustion**: under
ferromagnetic `0 ≤ J, 0 < β`,
`freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) ⟨J, 0, β⟩ - log 2 ≤ β·J·d`.
ℤ^d concrete wrapper of Step 418 with `c = d`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_deviation_bound_exp
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_deviation_bound_exp
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-! ## Moved: ∞-vol f continuity-at-trivial-slice wrappers

The three wrappers
`freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_J_zero`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_beta_zero`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_bundle`
now live in `HighTemperatureBoundsFreeEnergyInfiniteContinuity.lean`. -/


/-! ## Moved: ℤ^d ∞-vol f deviation/ratio bundle wrappers

The 2 ℤ^d
`freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_deviation_sandwich_exp`
and `_ratio_bound_bundle` wrappers now live in
`...HighTemperatureBoundsFreeEnergyInfiniteDeviationAndRatio`.
The earlier import path is preserved by re-importing the new child. -/



end Ambient

end IsingModel
