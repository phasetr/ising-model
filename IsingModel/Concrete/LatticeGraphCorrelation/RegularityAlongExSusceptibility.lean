import IsingModel.Lattice
import IsingModel.AmbientLattice.BetaDerivativePartitionSusc
import IsingModel.AmbientLattice.JDerivative
import IsingModel.AmbientLattice.FieldDerivative

/-!
# ℤ^d differentiability of the along-exhaustion susceptibility in one parameter

Concrete `latticeGraph d` statements that, at a fixed site of `Fin d → ℤ` and a fixed stage
of an arbitrary `Ambient.Exhaustion`, the susceptibility of that stage has a derivative in
one parameter of the record at a prescribed value, the others being held fixed. The inverse
temperature is treated at zero external field and again at an unrestricted one; the coupling
and the external field are each treated at unrestricted parameters. Every statement is in
existence form and requires a `Fintype` instance on the edge set induced at every stage;
that instance is its entire requirement, since no `Prop`-typed hypothesis is carried here.

Reference: Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5--§17.6, where the correlation
functions are differentiated in the parameter and the existence of such derivatives is stated.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in β at h = 0**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_beta_gen
    (IsingModel.latticeGraph d) Λ J β i n


/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in β at general h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun β' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) c β :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_beta_general_h_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in J**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun J' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) c J :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_J_gen
    (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d along-ex: `susceptibilityAlongExhaustion` HasDerivAt in h**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_hasDerivAt_field
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    ∃ c : ℝ, HasDerivAt (fun h' =>
        Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) c h :=
  Ambient.susceptibilityAlongExhaustion_hasDerivAt_field_gen
    (IsingModel.latticeGraph d) Λ J h β i n



end Ambient
end IsingModel
