import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperSandwichLogZ

/-!
# Concrete alongExhaustion sharper-exp Z/f/log Z wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete alongExhaustion
sharper-exp upper-bound / sandwich / complete-summary wrappers on
`latticeGraph d` at `h = 0`. 17 theorems for
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_*_exp`, and
`log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_*_exp`
families plus ferromagnetic variants. The theorem names are unchanged
from the former `HighTemperatureBounds` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex sharper Z upper bound at stage `n`**: under `0 ≤ β·J`,
`Z_n ≤ 2^|Λ_n| · exp(β·J·|E_n|)`. ℤ^d wrapper. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex sharper freeEnergy upper bound at stage `n`**: under
`0 < |Λ_n|` and `0 ≤ β·J`, `f_n ≤ log 2 + β·J·|E_n|/|Λ_n|`. ℤ^d wrapper. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex sharper log Z upper bound at stage `n`**: under
`0 ≤ β·J`, `log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`. ℤ^d wrapper. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex sharper log Z sandwich at stage `n`**: under `0 ≤ β·J`,
`|Λ_n|·log 2 + |E_n|·log cosh(β·J) ≤ log Z_n ≤ |Λ_n|·log 2 + β·J·|E_n|`.
ℤ^d wrapper. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich_exp
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n) ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_sandwich_exp
    (IsingModel.latticeGraph d) Λ J β hβJ n
/-! ## Moved: ℤ^d HT AlongExhaustion ferromagnetic upper_bound_exp wrappers

The three ferromagnetic alongExhaustion sharper-exp HT upper-bound
wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExhaustionExpSharperFerro`.
The earlier import path is preserved by re-importing the new child. -/


/-! ## Moved: ℤ^d HT AlongExhaustion sandwich_exp wrappers

The 4 ℤ^d along-exhaustion sandwich_exp HT wrappers
(`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_sandwich_exp`,
`_ferromagnetic`,
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_sandwich_exp`,
`_ferromagnetic`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExExpSharperSandwich`.
The earlier import path is preserved by re-importing the new child.
-/

/-! ## Moved: ℤ^d HT AlongExhaustion complete_summary_exp wrappers

The 6 ℤ^d along-exhaustion `*_complete_summary_exp` HT wrappers
(3 base: `freeEnergyAlongExhaustion_*`, `partitionFunctionAlongExhaustion_*`,
`log_partitionFunctionAlongExhaustion_*`; plus 3 `_ferromagnetic`
variants) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsAlongExExpSharperCompleteSummary`.
The earlier import path is preserved by re-importing the new child.
-/


end Ambient

end IsingModel
