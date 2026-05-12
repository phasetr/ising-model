import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity

/-!
# Concrete AlongExhaustion Mayer strict positivity wrappers

Narrow child module for ten ℤ^d AlongExhaustion strict-positivity /
strict-monotonicity wrappers under `allPolymers` nonempty hypotheses.
Each wrapper is a thin pass-through to the corresponding ambient
`*_AlongExhaustion_*_of_polymers_nonempty` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_lt_of_lt_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_lt_of_lt_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly hs hst

/-- **ℤ^d along-ex: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_strictMonoOn_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ n h_poly

/-- **ℤ^d along-ex: 0 < pFE under `0 < t` and polymers exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos n h_poly

/-- **ℤ^d along-ex: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_gt_one_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_gt_one_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos n h_poly

/-- **ℤ^d along-ex: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos n h_poly

/-- **ℤ^d along-ex: 0 < pFE(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
          (Real.tanh (β * J)) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_tanh_pos n h_poly

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
