import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Concrete along-exhaustion joint regularity wrappers

Narrow child module for six ℤ^d along-exhaustion joint regularity
wrappers (`*_continuous_joint` / `*_differentiable_joint` for
`correlation`, `magnetization`, and `susceptibility`). Each wrapper is
a thin pass-through to the corresponding ambient
`*AlongExhaustion_{continuous,differentiable}_joint*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
