import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity

/-!
# Concrete free-energy per-direction analyticity wrappers

This module contains `latticeGraph` wrappers for per-direction free-energy
`AnalyticAt` and `AnalyticOnNhd` APIs at the finite-volume and
along-exhaustion layers. It is split out of the legacy concrete correlation
module so downstream users can import the free-energy analyticity surface
without pulling the whole legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume free-energy per-direction analyticity -/

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) β :=
  Ambient.freeEnergyΛ_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) J :=
  Ambient.freeEnergyΛ_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
`h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, 0, β'⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
`h = 0`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', 0, β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) β :=
  Ambient.freeEnergyΛ_analyticAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) J :=
  Ambient.freeEnergyΛ_analyticAt_J_general_h
    (IsingModel.latticeGraph d) Λ β h J

/-- **ℤ^d Λ: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticAt_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) h :=
  Ambient.freeEnergyΛ_analyticAt_h
    (IsingModel.latticeGraph d) Λ J β h

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_beta_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J h : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h, β'⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_beta_general_h
    (IsingModel.latticeGraph d) Λ J h

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_J_general_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β h : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J', h, β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_J_general_h
    (IsingModel.latticeGraph d) Λ β h

/-- **ℤ^d Λ: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_latticeGraph_analyticOnNhd_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      Ambient.freeEnergyΛ (IsingModel.latticeGraph d) Λ
        ⟨J, h', β⟩) Set.univ :=
  Ambient.freeEnergyΛ_analyticOnNhd_h
    (IsingModel.latticeGraph d) Λ J β

/-! ### ℤ^d along-exhaustion free-energy per-direction analyticity -/

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) β :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_beta_h_zero
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_J_h_zero
    (IsingModel.latticeGraph d) Λ β J n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, 0, β'⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_beta_h_zero
    (IsingModel.latticeGraph d) Λ J n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', 0, β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_J_h_zero
    (IsingModel.latticeGraph d) Λ β n

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) β :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_beta_general_h
    (IsingModel.latticeGraph d) Λ J h β n

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) J :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_J_general_h
    (IsingModel.latticeGraph d) Λ β h J n

/-- **ℤ^d along-ex: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β h : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) h :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_h
    (IsingModel.latticeGraph d) Λ J β h n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at general `h`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at general `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_h
    (IsingModel.latticeGraph d) Λ J β n

end Ambient
end IsingModel
