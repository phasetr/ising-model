import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity

/-!
# Concrete polymer free-energy analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `polymerFreeEnergy` analytic wrappers. The theorem
names are the same as the former legacy declarations, but callers can now
import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.6 polymerFreeEnergy tanh analytic ℤ^d wraps -/

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β' * J))) β :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J'))) J :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticOnNhd
on (Set.Ici 0) in β under `0 ≤ J`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β' * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    (IsingModel.latticeGraph d) Λ hJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticOnNhd
on (Set.Ici 0) in J under `0 ≤ β`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_J_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J'))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    (IsingModel.latticeGraph d) Λ hβ

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β' * J))) β :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J'))) J :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticOnNhd
on (Set.Ici 0) in β under `0 ≤ J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β' * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero
    (IsingModel.latticeGraph d) Λ hJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticOnNhd
on (Set.Ici 0) in J under `0 ≤ β`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J'))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero
    (IsingModel.latticeGraph d) Λ hβ n

/-- **ℤ^d Λ: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) Λ) s) t :=
  Ambient.polymerFreeEnergy_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) Λ) s) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d along-ex: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
