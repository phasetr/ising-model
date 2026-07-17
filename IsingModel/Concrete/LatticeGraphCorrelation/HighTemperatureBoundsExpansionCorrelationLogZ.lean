import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperClosed

/-!
# Concrete HT correlation + log Z closed-form wrappers

Narrow child module for the 3 ℤ^d HT correlation / log-partition
closed-form wrappers
(`correlationΛ_latticeGraph_high_temp_expansion_h_zero_closed`,
`log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed`,
`log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed`)
extracted from `HighTemperatureBoundsExpansion.lean` in PR #2069.
Each is a thin pass-through to the corresponding ambient
`correlationΛ_high_temp_expansion_h_zero_closed` /
`log_partitionFunctionΛ_high_temp_expansion_h_zero_closed` /
`log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`
lemma at `IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsExpansion` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d high-temperature correlation closed form (FV §3.7.3 eq. (3.46))**:
on the ℤ^d induced subgraph at zero external field,
`⟨σ_A⟩^Λ_{β,0} = (∑_{X : ∂X=A} tanh^|X|) / (∑_{X : ∂X=∅} tanh^|X|)`.
ℤ^d wrapper of `correlationΛ_high_temp_expansion_h_zero_closed`. -/
theorem correlationΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset ↑Λ) :
    correlationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A
      = (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
        (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlationΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β A

/-- **ℤ^d log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`log Z_Λ(⟨J, 0, β⟩) = |Λ| · log 2 + |E_Λ| · log(cosh βJ) + log(∑_{X even} tanh^|X|)`.
ℤ^d wrapper of `log_partitionFunctionΛ_high_temp_expansion_h_zero_closed`. -/
theorem log_partitionFunctionΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ))
      = (Λ.card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d along-exhaustion log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`, at every stage `n`,
`log Z_n(⟨J, 0, β⟩) = |Λ_n| · log 2 + |E_n| · log(cosh βJ) + log(∑ tanh^|X|)`.
ℤ^d wrapper of `log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ n

end Ambient

end IsingModel
