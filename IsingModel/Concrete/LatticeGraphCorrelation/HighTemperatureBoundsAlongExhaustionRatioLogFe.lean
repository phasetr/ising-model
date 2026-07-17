import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe

/-!
# ℤ^d alongExhaustion log Z + freeEnergy ratio sandwich / bound wrappers at h = 0

Narrow child module for 14 §18.3-§18.4 concrete (`latticeGraph d`)
alongExhaustion `log_partitionFunction` and `freeEnergy`
ratio_sandwich / ratio_bound (+ deviation_pos / pow_two_lt)
wrappers at h = 0 (with J = 0 / β = 0 trivial slices and
ferromagnetic variants). Theorem names are unchanged from the former
`HighTemperatureBoundsAlongExhaustionRatioBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d along-ex f ratio sandwich bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex ferromagnetic f ratio sandwich bundle at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
        (Λ.volume n).card * Real.log (Real.cosh (β * J))
        ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n
            - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n
          - freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card) :=
  freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_sandwich_bundle
    d Λ J β (mul_nonneg hβ.le hJ) n hne

/-- **ℤ^d along-ex log Z ratio sandwich bundle at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex ferromagnetic log Z ratio sandwich bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_sandwich_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨0, 0, β⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) ∧
    (((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
        Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n)
            - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, 0⟩ : IsingParams ℝ) n) ∧
      Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n)
          - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n)
          ≤ β * J *
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_sandwich_bundle
    d Λ J β (mul_nonneg hβ.le hJ) n

/-! ## Moved: ratio_bound_bundle wrappers

The four `ratio_bound_bundle` wrappers
(`log_partitionFunctionAlongExhaustion_latticeGraph_*_ratio_bound_bundle`
and `freeEnergyAlongExhaustion_latticeGraph_*_ratio_bound_bundle`,
each with `_ferromagnetic` variants) now live in
`HighTemperatureBoundsAlongExhaustionRatioBoundBundle.lean`. -/



/-! ## Moved: freeEnergyAlongExhaustion deviation bound wrappers

The two
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_*`
wrappers (`bound_exp_of_nonempty`, `pos_of_nonempty`) now live in
`HighTemperatureBoundsAlongExhaustionRatioLogFeDeviation.lean`. -/



/-! ## Moved: freeEnergyAlongEx ratio_bound wrappers

The four
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_ratio_bound`
wrappers (`{,_beta_zero,_ferromagnetic,_beta_zero_ferromagnetic}`)
now live in `HighTemperatureBoundsAlongExRatioLogFeBound.lean`. -/


end Ambient

end IsingModel
