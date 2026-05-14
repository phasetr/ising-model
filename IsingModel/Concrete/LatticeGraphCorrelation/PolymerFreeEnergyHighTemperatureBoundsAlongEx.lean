import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds

/-!
# ℤ^d §18.5 AlongExhaustion polymer free-energy high-temperature bounds

Narrow child module for six ℤ^d AlongExhaustion polymer free-energy
high-temperature bound wrappers extracted from
`PolymerFreeEnergyHighTemperatureBounds.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_of_nonneg`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_monotoneOn_Ici_zero`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_le_of_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_eps_of_betaJ_nonneg`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_le_pow_sub_one_betaJ`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_lt_log_two_of_pow_lt_two`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdSum sandwich for `t ≥ 0`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_le_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-! ## Moved: along-ex polymerFreeEnergyAlongExhaustion tanh bound wrappers

The three along-ex `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*`
bound wrappers (`_le_eps`, `_le_pow_sub_one`, `_lt_log_two_of_pow_lt_two`)
now live in `PolymerFreeEnergyHighTemperatureBoundsAlongExPFE.lean`. -/



end Ambient
end IsingModel
