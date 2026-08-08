import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d translation-shift invariance wrappers

Instantiates translation invariance at `IsingModel.latticeGraph d`: the free energy along an
exhaustion and in infinite volume, and the along-exhaustion correlation of a translated
observation set. Each is a pass-through of the corresponding abstract
translation-invariance lemma.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d freeEnergyAlongExhaustion shift translation invariance**:
`freeEnergyAlongExhaustion (Λ.shift t) n = freeEnergyAlongExhaustion Λ n`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p n
      = freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_shift_eq (IsingModel.latticeGraph d) Λ t p n

/-- **ℤ^d freeEnergyInfinite shift translation invariance**:
`freeEnergyInfinite (Λ.shift t) = freeEnergyInfinite Λ`. -/
theorem freeEnergyInfinite_latticeGraph_shift_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) (Λ.shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d) Λ t p

/-- **ℤ^d free-energy shift invariance**:
`freeEnergyInfinite (latticeGraph d) ((cubicExhaustion d).shift t) p
  = freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_shift
    (d : ℕ) (t : Fin d → ℤ) (p : IsingParams ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        ((Ambient.cubicExhaustion d).shift t) p
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) p :=
  freeEnergyInfinite_shift_eq (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) t p

/-- **ℤ^d correlationAlongExhaustion shift translation invariance**:
`correlationAlongExhaustion (Λ.shift t) (vaddFinset t A) n = correlationAlongExhaustion Λ A n`. -/
theorem correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (t : Fin d → ℤ)
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      ((Λ.shift t).volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ)) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) (Λ.shift t) p
        (vaddFinset t A) n
      = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p A n :=
  correlationAlongExhaustion_shift_vaddFinset_eq
    (IsingModel.latticeGraph d) Λ t p A n

end Ambient

end IsingModel
