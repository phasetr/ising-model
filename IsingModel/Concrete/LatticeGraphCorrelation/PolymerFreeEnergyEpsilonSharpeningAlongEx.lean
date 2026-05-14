import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening

/-!
# ℤ^d AlongExhaustion polymer free-energy epsilon-sharpening wrappers

Narrow child module for six ℤ^d AlongExhaustion polymer free-energy
epsilon-sharpening wrappers extracted from
`PolymerFreeEnergyEpsilonSharpening.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_nonneg_of_nonneg`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pow_at_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_eq_zero_iff_eps_eq_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_pos_iff_eps_pos`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_lt_eps_iff_eps_pos`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_lt_pow_sub_one_of_eps_pos`.
-/

namespace IsingModel
namespace Ambient

/-- **Z^d along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hk n

/-! ## Moved: along-ex polymerFreeEnergyAlongExhaustion ε(t) wrappers

The four along-ex `polymerFreeEnergyAlongExhaustion_latticeGraph_*`
ε(t)-sharpening wrappers (`_eq_zero_iff`, `_pos_iff`, `_lt_eps_iff`,
`_lt_pow_sub_one`) now live in
`PolymerFreeEnergyEpsilonSharpeningAlongExPFE.lean`. -/




end Ambient
end IsingModel
