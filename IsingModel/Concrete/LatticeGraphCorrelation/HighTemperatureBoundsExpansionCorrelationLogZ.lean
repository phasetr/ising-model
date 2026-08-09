import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperClosed

/-!
# ℤ^d closed forms for the correlation and for `log Z` at zero field (§18.3)

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the
high-temperature closed form of the correlation on a fixed finite volume `Λ` as the ratio of
the edge-subset sum of `tanh (β * J) ^ |X|` over subsets whose parity matches the observable
to the same sum over even subsets; and the decomposition of `log Z` as
`|Λ| * log 2 + |E_Λ| * log (cosh (β * J))` plus the logarithm of the even-subgraph sum, on a
fixed volume and at a stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`. The correlation
closed form holds with no condition on `J` or `β`; each decomposition of `log Z` assumes
`0 ≤ β * J`.
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
