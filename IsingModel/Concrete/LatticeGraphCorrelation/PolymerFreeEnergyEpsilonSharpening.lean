import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# ℤ^d Λ cluster-expansion remainder ε(t) and its strict ceiling (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the basic facts about the
cluster-expansion remainder `ε(t)`, the activity sum over the nonempty members of
`vdCompatiblePolymerFamilies`: its sign for `0 ≤ t`, the vanishing of its positive powers at
`t = 0`, and, again for `0 ≤ t`, the strict ceiling by `(1 + t) ^ |E| − 1` that a positive
remainder buys for the polymer free energy. These sharpen the GJ §18.5 polymer free-energy
bounds on ℤ^d away from the `tanh` parametrization.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 ε(t) sign/vanishing + non-tanh polymerFreeEnergy sharpening ℤ^d wraps -/

/-- **Z^d Λ: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hn

/-- **Z^d Λ: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t`, ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_latticeGraph_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t <
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ ht h_eps_pos

end Ambient
end IsingModel
