import IsingModel.AmbientLatticeSumFInfHSymMono
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Evenness in the external field of the ℤ^d infinite-volume free energy

Concrete `IsingModel.latticeGraph d` statements about `freeEnergyInfinite`, the limit
superior of the free energy along an exhaustion.

Reversing the sign of the external field leaves the value unchanged, so the value at a
field equals the value at its absolute value. Both readings are stated along an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ` and again along `Ambient.cubicExhaustion d`, and none
of them takes a hypothesis or an instance argument.

Monotonicity in the size of the external field is the one statement here that takes either.
Along the cubic exhaustion, a non-negative coupling and a positive inverse temperature make
the value monotone under `|h₁| ≤ |h₂|`; it requires `Nonempty (Fin d → ℤ)` as an instance
argument, and its proof supplies the ambient monotonicity statement with the constant `d`,
discharging the side condition by the handshake bound `|E| ≤ d · |Λ|` for the graph the
lattice induces at each stage volume.
-/

namespace IsingModel
namespace Ambient

/-- **`|h|`-monotonicity of `freeEnergyInfinite` on ℤ^d**:
`|h₁| ≤ |h₂| ⇒ freeEnergyInfinite ⟨J, h₁, β⟩ ≤ freeEnergyInfinite ⟨J, h₂, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_abs_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  refine freeEnergyInfinite_monotone_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_ hh
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d**:
`freeEnergyInfinite ⟨J, -h, β⟩ = freeEnergyInfinite ⟨J, h, β⟩`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_neg_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_abs_h
    (d : ℕ) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h β

/-- **h-evenness of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_neg_h (IsingModel.latticeGraph d) Λ J h β

/-- **`|h|`-form of `freeEnergyInfinite` on ℤ^d** (any Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h β : ℝ) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) :=
  freeEnergyInfinite_eq_abs_h (IsingModel.latticeGraph d) Λ J h β

end Ambient

end IsingModel
