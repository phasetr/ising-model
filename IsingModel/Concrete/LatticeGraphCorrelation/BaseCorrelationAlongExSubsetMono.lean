import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d per-stage correlation along the cubic exhaustion

Concrete `IsingModel.latticeGraph d` statements along `Ambient.cubicExhaustion d`.

At a stage whose volume contains the site set, the correlation along the exhaustion is the
finite-volume correlation of that set inside the stage volume; at a stage whose volume does
not contain it, the value is `0`. Each of those reads is stated under exactly the
containment hypothesis it names and under no other. Under `Ferromagnetic` on the parameter
record the stage index enters monotonically: the correlation of a fixed site set does not
decrease as the stage grows. No instance argument is taken.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationAlongExhaustion of_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n
      = correlationΛ (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).volume n) p (liftFinset A hA) :=
  correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion of_not_subset unfolding**. -/
theorem correlationAlongExhaustion_latticeGraph_of_not_subset
    (d : ℕ) (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} {n : ℕ}
    (hA : ¬ A ⊆ (Ambient.cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p A n = 0 :=
  correlationAlongExhaustion_of_not_subset (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hA

/-- **ℤ^d correlationAlongExhaustion stage-index Monotone**. -/
theorem correlationAlongExhaustion_latticeGraph_cubicExhaustion_monotone
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (Fin d → ℤ)) :
    Monotone (correlationAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p A) :=
  correlationAlongExhaustion_monotone (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf A

end Ambient

end IsingModel
