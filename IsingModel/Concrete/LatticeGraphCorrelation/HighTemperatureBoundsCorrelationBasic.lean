import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete correlationΛ pair / singleton high-temperature wrappers at h = 0

Narrow child module for the §18.3-§18.4 concrete `correlationΛ_latticeGraph`
basic high-temperature wrappers at `h = 0`: pair nonneg, pair `≤ 1`,
singleton / pair trivial-slice vanishings at `J = 0` and `β = 0`, pair
sandwich, singleton / pair ferromagnetic, singleton `= 0 ∧ ≤ 1`, and the
pair+singleton bundle. Bundle / single-edge-bound / capstone / §18.7
exponential-decay wrappers remain in the parent `HighTemperatureBounds`.
The theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ-level pair correlation nonneg at h = 0**:
under `0 ≤ β·J`, `0 ≤ correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j}`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : ↑Λ) :
    0 ≤ correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) :=
  correlationΛ_high_temp_h_zero_at_pair_nonneg
    (IsingModel.latticeGraph d) Λ J β hβJ i j

/-- **ℤ^d Λ-level pair correlation ≤ 1**:
`correlationΛ (latticeGraph d) Λ ⟨J, 0, β⟩ {i, j} ≤ 1`. -/
theorem correlationΛ_latticeGraph_high_temp_h_zero_at_pair_le_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset ↑Λ) ≤ 1 :=
  correlationΛ_high_temp_h_zero_at_pair_le_one
    (IsingModel.latticeGraph d) Λ J β i j

/-! ## Moved: trivial-slice wrappers (J = 0, β = 0)

The four `correlationΛ_latticeGraph_high_temp_h_zero_at_*_{J,beta}_zero`
trivial-slice wrappers (singleton/pair at J = 0 and β = 0) now live in
`HighTemperatureBoundsCorrelationBasicTrivialSlices.lean`. -/


/-! ## Moved: pair sandwich / ferromagnetic / bundle wrappers

The five `correlationΛ_latticeGraph_high_temp_h_zero_*` wrappers
(`pair_sandwich`, `singleton_ferromagnetic`, `pair_ferromagnetic`,
`singleton_eq_zero_le_one`, `pair_singleton_bundle`) now live in
`HighTemperatureBoundsCorrelationBasicBundles.lean`. -/



end Ambient

end IsingModel
