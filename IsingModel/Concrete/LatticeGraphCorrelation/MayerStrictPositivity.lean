import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaEpsilonIff

/-!
# Concrete Mayer strict positivity wrappers

Narrow child module for concrete `ℤ^d` strict-monotonicity and strict
positivity wrappers under `allPolymers` nonempty hypotheses. This keeps callers
that only need these forwarders out of the monolithic lattice-correlation
original module.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅ ℤ^d
wraps -/

/-- **ℤ^d Λ: vdSum(s) < vdSum(t) under polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_lt_of_lt_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly hs hst

/-- **ℤ^d Λ: vdSum is `StrictMonoOn (Set.Ici 0)`**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_strictMonoOn_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_poly

/-! ## Moved: polymerFreeEnergy_Λ_pos_of_t_pos wrapper

`polymerFreeEnergy_Λ_latticeGraph_pos_of_t_pos_of_polymers_nonempty`
now lives in `MayerStrictPositivityPFE.lean`. -/


/-- **ℤ^d Λ: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_gt_one_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos h_poly

/-- **ℤ^d Λ: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pos_of_t_pos_of_polymers_nonempty
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (IsingModel.latticeGraph d) Λ h_t_pos h_poly

/-! ## Moved: polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos wrapper

`polymerFreeEnergy_Λ_latticeGraph_tanh_pos_of_tanh_pos_of_polymers_nonempty`
now lives in `MayerStrictPositivityPFE.lean`. -/


/-! ## Moved: Λ-tanh / strictMono mayer wrappers

The four Λ-tanh / strictMono mayer wrappers
(`vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_of_tanh_pos_of_polymers_nonempty`,
`_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty`,
`polymerFreeEnergy_Λ_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty`,
`vdPolymerFamilies_sum_Λ_latticeGraph_strictMonoOn_Ioi_zero_of_polymers_nonempty`)
now live in `MayerStrictPositivityTanhAndStrictMono.lean`. -/



/-! ## Moved: AlongExhaustion strict-positivity / strictMono wrappers

The ten AlongExhaustion `*_polymers_nonempty` wrappers
(`vdPolymerFamilies_sumAlongExhaustion_*` and
`polymerFreeEnergyAlongExhaustion_*`) now live in
`MayerStrictPositivityAlongEx.lean`. -/


end Ambient
end IsingModel
