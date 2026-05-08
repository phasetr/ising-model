import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Concrete joint regularity wrappers

This module contains concrete `latticeGraph` specializations of joint
`Continuous`, `Differentiable`, `ContinuousAt`, and `DifferentiableAt` APIs for
correlation, magnetization, and susceptibility. It is split out of the legacy
concrete correlation module so downstream users can depend on a narrower child
path.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Λ-layer and along-exhaustion joint wrappers -/

/-- **ℤ^d Λ: correlationΛ jointly Continuous in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_continuous_joint (IsingModel.latticeGraph d) Λ A

/-- **ℤ^d Λ: correlationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  Ambient.correlationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ A

/-- **ℤ^d Λ: magnetizationΛ jointly Continuous in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: magnetizationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Continuous in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_continuous_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) :=
  Ambient.correlationAlongExhaustion_differentiable_joint_gen
    (IsingModel.latticeGraph d) Λ A n

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.magnetizationAlongExhaustion_continuous_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.magnetizationAlongExhaustion_differentiable_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly Continuous in `(β, J, h)`**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.susceptibilityAlongExhaustion_continuous_joint_gen
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) :=
  Ambient.susceptibilityAlongExhaustion_differentiable_joint_gen
    (IsingModel.latticeGraph d) Λ i n

/-! ### ℤ^d joint pointwise wrappers -/

/-- **ℤ^d Λ: correlationΛ jointly ContinuousAt**. -/
theorem correlationΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ A p

/-- **ℤ^d Λ: correlationΛ jointly DifferentiableAt**. -/
theorem correlationΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ A p

/-- **ℤ^d Λ: magnetizationΛ jointly ContinuousAt**. -/
theorem magnetizationΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.magnetizationΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: magnetizationΛ jointly DifferentiableAt**. -/
theorem magnetizationΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.magnetizationΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: susceptibilityΛ jointly ContinuousAt**. -/
theorem susceptibilityΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.susceptibilityΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: susceptibilityΛ jointly DifferentiableAt**. -/
theorem susceptibilityΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.susceptibilityΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly ContinuousAt**. -/
theorem correlationAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  Ambient.correlationAlongExhaustion_continuousAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n p

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly DifferentiableAt**. -/
theorem correlationAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ A n) p :=
  Ambient.correlationAlongExhaustion_differentiableAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n p

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly ContinuousAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.magnetizationAlongExhaustion_continuousAt_joint
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly DifferentiableAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.magnetizationAlongExhaustion_differentiableAt_joint
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly ContinuousAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.susceptibilityAlongExhaustion_continuousAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n p

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly DifferentiableAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨q.2.1, q.2.2, q.1⟩ i n) p :=
  Ambient.susceptibilityAlongExhaustion_differentiableAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n p

end Ambient
end IsingModel
