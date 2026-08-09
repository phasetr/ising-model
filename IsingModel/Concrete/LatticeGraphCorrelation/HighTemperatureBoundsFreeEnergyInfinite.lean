import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d infinite-volume free energy under a bounded edge density at zero field

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, upper bounds
on `freeEnergyInfinite` — the `limsup` of the finite-volume free-energy densities along an
exhaustion. For an arbitrary `Ambient.Exhaustion` of `Fin d → ℤ` the bound is
`log 2 + β * J * c`, where `c` is a caller-supplied constant bounding the edge count of every
nonempty stage by `c` times its site count. For `Ambient.cubicExhaustion d` that constant is
taken to be `d`, giving the bound `log 2 + β * J * d`, the sandwich of `freeEnergyInfinite`
between `log 2` and that bound, the bundle adding to the sandwich the value `log 2` taken at
`⟨0, 0, β⟩` and at `⟨J, 0, 0⟩`, and the deviation form
`freeEnergyInfinite - log 2 ≤ β * J * d`. Every statement here assumes `0 ≤ J` together with
`0 < β`, and the cubic ones obtain the edge-density constant from
`inducedLatticeGraph_card_edgeFinset_le`.
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

end Ambient

end IsingModel
