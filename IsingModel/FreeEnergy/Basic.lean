import IsingModel.InfiniteVolume
import IsingModel.LeeYang
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Free energy definitions

Mechanical child split from `IsingModel.FreeEnergy`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Free energy definition (equation 4.6.1) -/

/-- **Free energy per site** (Glimm–Jaffe, (4.6.1), p. 67):
`f = |ι|⁻¹ · ln Z`. Well-defined since `Z > 0` (`partitionFunction_pos`). -/
noncomputable def freeEnergy (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G p)

/-- The free energy as a function of the coupling constant `J`,
with `h` and `β` fixed. -/
noncomputable def freeEnergyJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) : ℝ → ℝ :=
  fun J => freeEnergy G ⟨J, h, β⟩

/-- The free energy as a function of the external field `h`,
with `J` and `β` fixed. -/
noncomputable def freeEnergyH (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) : ℝ → ℝ :=
  fun h => freeEnergy G ⟨J, h, β⟩

end IsingModel
