import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFreeEnergy

/-!
# ℤ^d strict free-energy ceiling in the cluster-expansion convergence regime (§18.5)

Instantiates at `IsingModel.latticeGraph d`, at the parameter record `⟨J, 0, β⟩`, the strict
upper bound placing the free-energy density below
`log 2 + (|E| / |Λ|) * log (cosh (β * J)) + log 2 / |Λ|`, on a fixed finite volume and at a
stage `n` of an `Ambient.Exhaustion` of `Fin d → ℤ`. Each version is stated under `0 ≤ β * J`
and again in a ferromagnetic form under `0 ≤ J` together with `0 < β`, and every statement
here also assumes the volume nonempty and the convergence hypothesis
`(1 + tanh (β * J)) ^ |E| < 2`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: strict `freeEnergyΛ` upper bound in cluster-expansion
convergence regime** (§18.5 ℤ^d Λ wrap). -/
theorem freeEnergyΛ_latticeGraph_lt_log_two_plus_high_temp_correction
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card :=
  Ambient.freeEnergyΛ_lt_log_two_plus_high_temp_correction
    (IsingModel.latticeGraph d) Λ J β hβJ hne h_pow

/-- **ℤ^d Λ: strict `freeEnergyΛ` upper bound (ferromagnetic)**
(§18.5 ℤ^d Λ ferro wrap). -/
theorem freeEnergyΛ_latticeGraph_lt_log_two_plus_high_temp_correction_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ) /
          Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card :=
  freeEnergyΛ_latticeGraph_lt_log_two_plus_high_temp_correction
    d Λ J β (mul_nonneg hβ.le hJ) hne h_pow

/-- **ℤ^d along-ex: strict `freeEnergyAlongExhaustion` upper bound
in cluster-expansion convergence regime** (§18.5 ℤ^d along-ex wrap). -/
theorem
freeEnergyAlongExhaustion_latticeGraph_lt_log_two_plus_high_temp_correction
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card :=
  Ambient.freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction
    (IsingModel.latticeGraph d) Λ J β hβJ n hne h_pow

/-- **ℤ^d along-ex: strict `freeEnergyAlongExhaustion` upper bound
(ferromagnetic)** (§18.5 ℤ^d along-ex ferro wrap). -/
theorem
freeEnergyAlongExhaustion_latticeGraph_lt_log_two_plus_high_temp_correction_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card :=
  freeEnergyAlongExhaustion_latticeGraph_lt_log_two_plus_high_temp_correction
    d Λ J β (mul_nonneg hβ.le hJ) n hne h_pow

end Ambient
end IsingModel
