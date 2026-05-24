import IsingModel.FieldDerivative.Basic
import IsingModel.FreeEnergy.Basic

/-!
# Field derivative of free energy

Finite-volume free-energy continuity and differentiability in the external field.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Step 254: free energy h-derivative -/

/-- **Free energy h-derivative** (Step 254):
For any `(J, h, β)` and finite-volume Ising:

  `d/dh freeEnergy(h) = |ι|⁻¹ · β · gibbsExpectation(totalMagnetization)`

since `freeEnergy = |ι|⁻¹ · log(partitionFunction)` and
`d/dh log(Z) = Z'(h)/Z(h) = β·⟨M⟩` by the partition function h-derivative
(`hasDerivAt_partitionFunction_field`).

Reference: Glimm–Jaffe §17.6 / §4.6; standard thermodynamic identity
(magnetization per site = β⁻¹ · d/dh log(Z) / |ι|). -/
theorem hasDerivAt_freeEnergy_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ))
      ((Fintype.card ι : ℝ)⁻¹ *
        gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
          (fun σ => β * totalMagnetization σ)) h := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  have hZderiv := hasDerivAt_partitionFunction_field G J h β
  have hlogZ : HasDerivAt (fun h' => Real.log (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ)))
      ((∑ σ, β * totalMagnetization σ * boltzmannWeight G p σ) / partitionFunction G p) h := by
    have h := hZderiv.log hZne
    convert h using 1
  have hfreeE : (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) =
      (fun h' => (Fintype.card ι : ℝ)⁻¹ *
        Real.log (partitionFunction G (⟨J, h', β⟩ : IsingParams ℝ))) := by
    funext h'; rfl
  rw [hfreeE]
  have h := hlogZ.const_mul ((Fintype.card ι : ℝ)⁻¹)
  convert h using 1
  unfold gibbsExpectation
  field_simp

/-- **freeEnergy Continuous in h** (Step 256). -/
theorem freeEnergy_continuous_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    Continuous (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) :=
  continuous_iff_continuousAt.mpr fun h =>
    (hasDerivAt_freeEnergy_field G J h β).continuousAt

/-- **freeEnergy Differentiable in h** (Step 256). -/
theorem freeEnergy_differentiable_field
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    Differentiable ℝ (fun h' => freeEnergy G (⟨J, h', β⟩ : IsingParams ℝ)) :=
  fun h => (hasDerivAt_freeEnergy_field G J h β).differentiableAt

end IsingModel
