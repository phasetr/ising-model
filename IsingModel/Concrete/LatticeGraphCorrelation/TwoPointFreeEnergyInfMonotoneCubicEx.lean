import IsingModel.AmbientLatticeSumFInfHSymMono
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Parameter monotonicity of the ℤ^d infinite-volume free energy

Concrete `IsingModel.latticeGraph d` statements along `Ambient.cubicExhaustion d`. The
infinite-volume free energy is monotone in the coupling on `Set.Ici 0` assuming a
non-negative external field and a positive inverse temperature, in the external field on
`Set.Ici 0` assuming a non-negative coupling and a positive inverse temperature, and in the
inverse temperature on `Set.Ioi 0` assuming a non-negative coupling and a non-negative
external field.

Every statement requires `Nonempty (Fin d → ℤ)` as an instance argument, and each proof
supplies the ambient monotonicity statement with the constant `d`, discharging the side
condition by the handshake bound `|E| ≤ d · |Λ|` for the graph the lattice induces at each
stage volume.
-/

namespace IsingModel
namespace Ambient

/-- **J-monotonicity of `freeEnergyInfinite` on ℤ^d** under the concrete
BED constant `c = d` (PR #246). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **h-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  refine freeEnergyInfinite_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **β-monotonicity of `freeEnergyInfinite` on ℤ^d**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  refine freeEnergyInfinite_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)


end Ambient

end IsingModel
