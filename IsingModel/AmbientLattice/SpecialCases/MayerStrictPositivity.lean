import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer strict positivity wrappers along an exhaustion

Narrow child module for along-exhaustion strict-monotonicity and strict
positivity wrappers under `allPolymers` nonempty hypotheses. This keeps callers
that only need these forwarders out of the monolithic original special-cases
module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅ along-ex
wraps -/

/-- **Along-ex: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergyAlongExhaustion_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: pFE is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t) (Set.Ioi 0) :=
  polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-- **Along-ex: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    G (Λ.volume n) h_poly hs hst

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-- **Along-ex: vdSum is `StrictMonoOn (Set.Ioi 0)`**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    G (Λ.volume n) h_poly

/-- **Along-ex: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    G (Λ.volume n) h_t_pos h_poly

/-- **Along-ex: 1 < vdSum(tanh) under `0 < tanh` and polymers
exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

/-- **Along-ex: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J)) (n : ℕ)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph G (Λ.volume n))).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    G (Λ.volume n) h_tanh_pos h_poly

end Ambient
end IsingModel
