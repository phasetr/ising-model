/- TranslationShifts.lean
Narrow child module for the 8 ℤ^d shift / vaddFinset_eq wrappers
(`freeEnergyAlongExhaustion_latticeGraph_shift_eq`,
`freeEnergyInfinite_latticeGraph_shift_eq`,
`freeEnergyInfinite_latticeGraph_cubicExhaustion_shift`,
`correlationAlongExhaustion_latticeGraph_shift_vaddFinset_eq`,
`correlationΛ_latticeGraph_vaddFinset_eq`,
`partitionFunctionΛ_latticeGraph_vaddFinset_eq`,
`freeEnergyΛ_latticeGraph_vaddFinset_eq`,
`log_partitionFunctionΛ_latticeGraph_vaddFinset_eq`) extracted from
`Translation.lean` in PR #2062. Each is a thin pass-through to the
corresponding abstract translation-invariance lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `Translation` declarations.
-/
import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice

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

/-- **ℤ^d correlationΛ translation invariance**:
`⟨σ^{vadd A}⟩_{t +ᵥ Λ}(p) = ⟨σ^A⟩_Λ(p)` on ℤ^d. -/
theorem correlationΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ : Type _)) :
    correlationΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
        (A.map (vaddSubtypeEquiv t Λ).toEmbedding)
      = correlationΛ (IsingModel.latticeGraph d) Λ p A :=
  correlationΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p A

/-- **ℤ^d partitionFunctionΛ translation invariance**:
`Z_{t +ᵥ Λ}(p) = Z_Λ(p)` on ℤ^d. -/
theorem partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d freeEnergyΛ translation invariance**:
`f_{t +ᵥ Λ}(p) = f_Λ(p)` on ℤ^d. -/
theorem freeEnergyΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) (vaddFinset t Λ) p
      = freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_vaddFinset_eq (IsingModel.latticeGraph d) t Λ p

/-- **ℤ^d log_partitionFunctionΛ translation invariance**:
`log Z_{t +ᵥ Λ}(p) = log Z_Λ(p)` on ℤ^d. -/
theorem log_partitionFunctionΛ_latticeGraph_vaddFinset_eq
    (d : ℕ) (t : Fin d → ℤ) (Λ : Finset (Fin d → ℤ))
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
      (vaddFinset t Λ)).edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d)
        (vaddFinset t Λ) p)
      = Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) := by
  rw [partitionFunctionΛ_latticeGraph_vaddFinset_eq d t Λ p]


end Ambient

end IsingModel
