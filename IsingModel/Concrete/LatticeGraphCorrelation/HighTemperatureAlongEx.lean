import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperature

/-!
# Concrete polymerFreeEnergyAlongExhaustion cluster-expansion wrappers

Narrow child module for four ℤ^d non-ferromagnetic
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` wrappers
(`high_temp_sandwich`, `hasSum_via_log_of_pow_lt_two`, and tanh
variants). Each wrapper is a thin pass-through to the corresponding
ambient `polymerFreeEnergyAlongExhaustion_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy`** (§18.5 ℤ^d along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_high_temp_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)) t < Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ ht n h_pow

/-- **ℤ^d along-exhaustion: log Taylor expansion for `polymerFreeEnergy`**
(§18.5 ℤ^d along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t) :=
  Ambient.polymerFreeEnergyAlongExhaustion_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ ht n h_pow

/-- **ℤ^d along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy` (tanh form)** (§18.5 ℤ^d along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_high_temp_sandwich
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich
    (IsingModel.latticeGraph d) Λ hβJ n h_pow

/-- **ℤ^d along-exhaustion: log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 ℤ^d along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two
    (IsingModel.latticeGraph d) Λ hβJ n h_pow

end Ambient
end IsingModel
