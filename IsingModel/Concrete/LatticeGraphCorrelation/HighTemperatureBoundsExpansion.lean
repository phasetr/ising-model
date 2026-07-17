import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionVariants

/-!
# Concrete high-temperature partition-function and free-energy expansion wrappers

Narrow child module for the §18.3-§18.4 high-temperature partition-function
and free-energy expansion / closed-form / lower-bound / upper-bound /
`lower_le_upper` wrappers on `latticeGraph d`, plus the
`correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A` consistency check.
Sandwich and downstream wrappers remain in the parent
`HighTemperatureBounds`; sharper-exp wrappers were further split out into
`HighTemperatureBoundsExpSharper` in PR #1935; deviation / continuity
wrappers were further split out into `HighTemperatureBoundsDeviation` in
PR #1936; ratio_sandwich / ratio_bound wrappers were further split out
into `HighTemperatureBoundsRatioBounds` in PR #1937. The theorem names
are the same as the former declarations in `HighTemperatureBounds`, but
callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level partition function high-temperature expansion at `h = 0`**:
`Z_Λ(⟨J, 0, β⟩) = (cosh βJ)^|E_Λ| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`.
ℤ^d wrapper of `partitionFunctionΛ_high_temp_expansion_h_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card *
      ∑ σ : Config ↑Λ,
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionΛ_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d along-exhaustion partition function high-temperature expansion at `h = 0`**:
`Z_n(⟨J, 0, β⟩) = (cosh βJ)^|E_n| · ∑_σ ∏_e (1 + tanh(βJ) σ_iσ_j)`
at every stage `n`. ℤ^d wrapper of
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero`. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n =
      Real.cosh (β * J) ^
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card *
      ∑ σ : Config ↑(Λ.volume n),
        ∏ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
          (1 + Real.tanh (β * J) * edgeSpin σ e) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d FV (3.45) at `J = 0` consistency check**:
`Z_Λ(⟨0, 0, β⟩) = 2^|Λ|`. ℤ^d wrapper of
`partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero`. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_J_zero
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d FV (3.45) at `β = 0` consistency check**:
`Z_Λ(⟨J, 0, 0⟩) = 2^|Λ|`. ℤ^d wrapper. -/
theorem partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed_at_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Λ.card :=
  partitionFunctionΛ_high_temp_expansion_h_zero_closed_at_beta_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d FV (3.46) at `A = ∅` consistency check**:
under `0 ≤ β·J`,
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ ∅ = 1`.
ℤ^d wrapper of `correlationΛ_high_temp_h_zero_at_empty_A`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_empty_A
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) (∅ : Finset ↑Λ) = 1 :=
  correlationΛ_high_temp_h_zero_at_empty_A
    (IsingModel.latticeGraph d) Λ J β hβJ

/-! ## Moved: ℤ^d HT partition expansion general-h/closed/subset wrappers

The four wrappers
`partitionFunctionΛ_latticeGraph_high_temp_expansion`,
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_subset_form`
now live in `HighTemperatureBoundsExpansionGeneralH.lean`. -/


/-! ## Moved: ℤ^d HT correlation + log Z closed-form wrappers

The 3 ℤ^d
`correlationΛ_latticeGraph_high_temp_expansion_h_zero_closed`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed`,
and `log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed`
closed-form wrappers now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansionCorrelationLogZ`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d partitionFunction / freeEnergy HT lower/upper bound wrappers

The 5 ℤ^d HT partition-function / free-energy bound wrappers
(`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_upper_bound`,
`partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_upper_bound`,
`partitionFunctionΛ_latticeGraph_high_temp_h_zero_lower_le_upper`,
`freeEnergyΛ_latticeGraph_high_temp_h_zero_lower_le_upper`,
`partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_lower_bound`)
now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansionPartitionBounds`.
The earlier import path is preserved by re-importing the new child.
-/


/-! ## Moved: ℤ^d freeEnergyΛ / freeEnergyAlongExhaustion HT expansion + bound wrappers

The 5 ℤ^d `freeEnergyΛ_latticeGraph_*` /
`freeEnergyAlongExhaustion_latticeGraph_*` §18.3-§18.4
high-temperature wrappers
(`freeEnergyΛ_high_temp_expansion_h_zero_closed`,
`freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed`,
`freeEnergyΛ_high_temp_h_zero_upper_bound`,
`freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound`,
`freeEnergyΛ_high_temp_h_zero_lower_bound`) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsExpansionFreeEnergy`.
The earlier import path is preserved by re-importing the new child.
-/


end Ambient

end IsingModel
