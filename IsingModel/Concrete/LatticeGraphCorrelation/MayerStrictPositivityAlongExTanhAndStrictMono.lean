import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity

/-!
# ℤ^d AlongExhaustion tanh / strictMono mayer wrappers

Narrow child module for four ℤ^d AlongExhaustion tanh / strictMono mayer
wrappers extracted from `MayerStrictPositivityAlongEx.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_pos_polymers_nonempty`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: 1 < vdSum(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos n h_poly

/-- **ℤ^d along-ex: 0 < ε(tanh) under `0 < tanh` and polymers
exist**. (`_of_tanh_pos` hypothesis dropped from name to fit the
linter's 100-char budget; encoded in `h_tanh_pos` parameter.) -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_tanh_pos_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos n h_poly

/-- **ℤ^d along-ex: pFE is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)) t) (Set.Ioi 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly

/-- **ℤ^d along-ex: vdSum is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly

end Ambient
end IsingModel
