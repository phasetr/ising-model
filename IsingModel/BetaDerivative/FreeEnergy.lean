import IsingModel.BetaDerivative.Continuity

/-!
# Free energy beta derivatives

This module contains the free-energy beta derivative wrappers split from
`IsingModel.BetaDerivative`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Step 253: free energy β-derivative at general h -/

/-- **Free energy β-derivative at general h** (Step 253):
For any `(J, h, β)` and finite-volume Ising:

  `d/dβ freeEnergy(β) = |ι|⁻¹ · gibbsExpectation(-H)`

since `freeEnergy = |ι|⁻¹ · log(partitionFunction)` and
`d/dβ log(Z) = Z'(β)/Z(β) = ⟨-H⟩` by the partition function derivative
(`hasDerivAt_partitionFunction_beta`).

Reference: Glimm–Jaffe §4.6 (4.6.1) and §17.5; standard thermodynamic identity. -/
theorem hasDerivAt_freeEnergy_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    HasDerivAt (fun β' => freeEnergy G (⟨J, h, β'⟩ : IsingParams ℝ))
      ((Fintype.card ι : ℝ)⁻¹ * gibbsExpectation G (⟨J, h, β⟩ : IsingParams ℝ)
        (fun σ => - hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ)) β := by
  set p := (⟨J, h, β⟩ : IsingParams ℝ)
  have hZpos : 0 < partitionFunction G p := partitionFunction_pos G p
  have hZne : partitionFunction G p ≠ 0 := hZpos.ne'
  -- d/dβ log(Z(β)) = Z'(β)/Z(β)
  have hZderiv := hasDerivAt_partitionFunction_beta G J h β
  have hlogZ : HasDerivAt (fun β' => Real.log (partitionFunction G (⟨J, h, β'⟩ : IsingParams ℝ)))
      ((∑ σ, - hamiltonian G p σ * boltzmannWeight G p σ) / partitionFunction G p) β := by
    have h := hZderiv.log hZne
    convert h using 1
  -- freeEnergy = |ι|⁻¹ · log Z
  have hfreeE : (fun β' => freeEnergy G (⟨J, h, β'⟩ : IsingParams ℝ)) =
      (fun β' => (Fintype.card ι : ℝ)⁻¹ *
        Real.log (partitionFunction G (⟨J, h, β'⟩ : IsingParams ℝ))) := by
    funext β'; rfl
  rw [hfreeE]
  have h := hlogZ.const_mul ((Fintype.card ι : ℝ)⁻¹)
  convert h using 1
  -- Need: |ι|⁻¹ · gibbsExpectation(-H) = |ι|⁻¹ · (∑ -H · bw / Z)
  unfold gibbsExpectation
  field_simp

/-- **freeEnergy Continuous in β at general h** (Step 256). -/
theorem freeEnergy_continuous_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) :
    Continuous (fun β' => freeEnergy G (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  continuous_iff_continuousAt.mpr fun β =>
    (hasDerivAt_freeEnergy_beta_general_h G J h β).continuousAt

/-- **freeEnergy Differentiable in β at general h** (Step 256). -/
theorem freeEnergy_differentiable_beta_general_h
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) :
    Differentiable ℝ (fun β' => freeEnergy G (⟨J, h, β'⟩ : IsingParams ℝ)) :=
  fun β => (hasDerivAt_freeEnergy_beta_general_h G J h β).differentiableAt

end IsingModel
