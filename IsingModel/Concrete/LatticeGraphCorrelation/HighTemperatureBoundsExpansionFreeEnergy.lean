import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansionLowerUpperFE

/-!
# ℤ^d high-temperature decomposition and bounds for the free-energy density (§18.3)

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the
decomposition of the free-energy density as `log 2 + (|E| / |Λ|) * log (cosh (β * J))` plus
the logarithm of the even-subgraph sum divided by the site count, on a fixed finite volume and
at a stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`; the upper bound
`log 2 + (|E| / |Λ|) * log (2 * cosh (β * J))` in each of those scopes; and the lower bound
`log 2 + (|E_Λ| / |Λ|) * log (cosh (β * J))` on a fixed volume. Every statement here assumes
`0 ≤ β * J` and a nonempty volume.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ = log 2 + (|E_Λ|/|Λ|) · log(cosh βJ) + log(∑_{X even} tanh^|X|) / |Λ|`.
ℤ^d wrapper of `freeEnergyΛ_high_temp_expansion_h_zero_closed`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      = Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑Λ) =>
                  ∀ v : ↑Λ, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / Λ.card :=
  freeEnergyΛ_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d along-exhaustion freeEnergy high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`f_n = log 2 + (|E_n|/|Λ_n|) · log(cosh βJ) + log(∑ tanh^|X|) / |Λ_n|`.
ℤ^d wrapper of `freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_closed
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ (inducedGraph (IsingModel.latticeGraph d)
                  (Λ.volume n)).edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
                  ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_expansion_h_zero_closed
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 < |Λ|` and `0 ≤ β·J`,
`f_Λ ≤ log 2 + (|E_Λ|/|Λ|) · log(2 · cosh βJ)`. ℤ^d wrapper. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_upper_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
            Λ.card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyΛ_high_temp_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d along-exhaustion freeEnergy high-temperature upper bound (FV (3.45))**:
under `0 ≤ β·J` and `0 < |Λ_n|`, at every stage `n`,
`f_n ≤ log 2 + (|E_n|/|Λ_n|) · log(2 · cosh βJ)`. ℤ^d wrapper. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2
        + ((inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card : ℝ) /
            (Λ.volume n).card * Real.log (2 * Real.cosh (β * J)) :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d free-energy lower bound from FV (3.45)** at zero external field:
under `0 < |Λ|` and `0 ≤ β * J`,
`f_Λ(⟨J, 0, β⟩) ≥ log 2 + (|E_Λ|/|Λ|) · log(cosh(β·J))`.
ℤ^d wrapper of `freeEnergyΛ_high_temp_h_zero_lower_bound`. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_lower_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) :=
  freeEnergyΛ_high_temp_h_zero_lower_bound
    (IsingModel.latticeGraph d) Λ J β hβJ hne

end Ambient

end IsingModel
