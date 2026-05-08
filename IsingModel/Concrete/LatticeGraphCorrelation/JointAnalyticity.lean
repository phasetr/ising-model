import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity

/-!
# Concrete joint analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `AnalyticAt` / `AnalyticOnNhd` forwarders in the
joint `(β, J, h)` parameters. The theorem names are the same as the former
legacy declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d joint AnalyticAt + AnalyticOnNhd wrappers
(correlation / magnetization / susceptibility) at Λ + along-ex -/

/-- **ℤ^d Λ: magnetizationΛ jointly AnalyticAt**. -/
theorem magnetizationΛ_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) :=
  Ambient.magnetizationΛ_analyticAt_joint (IsingModel.latticeGraph d) Λ i β J h

/-- **ℤ^d Λ: magnetizationΛ jointly AnalyticOnNhd**. -/
theorem magnetizationΛ_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  Ambient.magnetizationΛ_analyticOnNhd_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly AnalyticAt**. -/
theorem susceptibilityΛ_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) :=
  Ambient.susceptibilityΛ_analyticAt_joint (IsingModel.latticeGraph d) Λ i β J h

/-- **ℤ^d Λ: susceptibilityΛ jointly AnalyticOnNhd**. -/
theorem susceptibilityΛ_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  Ambient.susceptibilityΛ_analyticOnNhd_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly AnalyticAt**. -/
theorem correlationAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) (β, J, h) :=
  Ambient.correlationAlongExhaustion_analyticAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n β J h

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly AnalyticOnNhd**. -/
theorem correlationAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) Set.univ :=
  Ambient.correlationAlongExhaustion_analyticOnNhd_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly AnalyticAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) :=
  Ambient.magnetizationAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ i n β J h

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly AnalyticOnNhd**. -/
theorem magnetizationAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  Ambient.magnetizationAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly AnalyticAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) :=
  Ambient.susceptibilityAlongExhaustion_analyticAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n β J h

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly AnalyticOnNhd**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  Ambient.susceptibilityAlongExhaustion_analyticOnNhd_joint_gen
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticOnNhd**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticOnNhd**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
