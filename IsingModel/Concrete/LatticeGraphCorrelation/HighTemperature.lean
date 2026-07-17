import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich

/-!
# Concrete high-temperature convergence wrappers for the lattice graph

Narrow child module for the §18.5 high-temperature sandwich,
convergence-radius `HasSum`, polymer-family sandwich, and strict free-energy
correction wrappers on `latticeGraph d`. The theorem names are the same as the
former declarations, but callers can now import this child module
directly.
-/

namespace IsingModel
namespace Ambient

/-! ## §18.5 cluster-expansion convergence-radius ℤ^d wraps -/

/-- **ℤ^d Λ-direct: high-temperature sandwich for `polymerFreeEnergy`**
(§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_high_temp_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 ∧
    (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ ht h_pow

/-- **ℤ^d Λ-direct: log Taylor expansion for `polymerFreeEnergy`**
(§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t) :=
  Ambient.polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ ht h_pow

/-- **ℤ^d Λ-direct: high-temperature sandwich for `polymerFreeEnergy`
(tanh form)** (§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_high_temp_sandwich
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ hβJ h_pow

/-- **ℤ^d Λ-direct: log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 ℤ^d wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) :=
  Ambient.polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ hβJ h_pow

/-! ## Moved: polymerFreeEnergyAlongExhaustion cluster-expansion wrappers

The four wrappers
`polymerFreeEnergyAlongExhaustion_latticeGraph_high_temp_sandwich`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log_of_pow_lt_two`,
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_high_temp_sandwich`, and
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two`
now live in `HighTemperatureAlongEx.lean`. -/


/-! ## Moved: vdPolymerFamilies sandwich wrappers

The four wrappers
`vdPolymerFamilies_sum_Λ_latticeGraph_sandwich(_sharp)?` and
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich(_sharp)?`
now live in `HighTemperatureVDPolymer.lean`. -/


/-! ## Moved: ferromagnetic cluster-expansion wrappers

The eight ferromagnetic wrappers
`polymerFreeEnergy_{Λ,AlongExhaustion}_latticeGraph_tanh_*_ferro` and
`vdPolymerFamilies_sum{_Λ,_AlongExhaustion}_latticeGraph_sandwich(_sharp)?(_ferromagnetic|_ferro)`
now live in `HighTemperatureFerromagnetic.lean`. -/


/-! ## Moved: `freeEnergy_lt_log_two_plus_high_temp_correction` wrappers

The four wrappers
`freeEnergyΛ_latticeGraph_lt_log_two_plus_high_temp_correction(_ferro)?`
and `freeEnergyAlongExhaustion_latticeGraph_lt_log_two_plus_high_temp_correction(_ferro)?`
now live in `HighTemperatureFreeEnergyCorrection.lean`. -/


end Ambient
end IsingModel
