import IsingModel.Inequalities.MonotonicityJBoundaryCondition
import IsingModel.Inequalities.GKSBoundaryCondition
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationFieldMonotone

/-!
# β-monotonicity of the `+` boundary single-spin correlation (FV §3.6, Issue #3605)

The `+` boundary single-spin correlation `⟨σ_x⟩⁺_Λ` is monotone increasing in the
inverse temperature `β`.  The proof uses the rescaling identity
`⟨F⟩⁺_{(J,h,β)} = ⟨F⟩⁺_{(βJ,βh,1)}` to reduce β-monotonicity to the already-proven
`J`-monotonicity (`gibbsExpectationBC_plus_monotone_J`, #3608) and `h`-monotonicity
(`gibbsExpectationBC_field_mono`, #3602): increasing `β` from `β₁` to `β₂` moves
`(β₁J, β₁h)` to `(β₂J, β₂h)` with both components non-decreasing.

* `boltzmannWeightBC_beta_rescale` / `gibbsExpectationBC_beta_rescale` — the rescaling.
* `gibbsExpectationBC_plus_monotone_beta_singleton` — `⟨σ_x⟩⁺_Λ` nondecreasing in `β`.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.6; Glimm–Jaffe Prop. 4.2.1.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **β-rescaling of the `+` boundary Boltzmann weight**: `w_{(J,h,β)} = w_{(βJ,βh,1)}`
(the inverse temperature factors into the couplings; the boundary indicator is
unchanged). -/
theorem boltzmannWeightBC_beta_rescale (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (η : Config ι) (σ : Config ι) :
    boltzmannWeightBC G β (fun _ => J) h Λ η σ
      = boltzmannWeightBC G 1 (fun _ => β * J) (β * h) Λ η σ := by
  have hbwJ : boltzmannWeightJ G β (fun _ => J) h
      = boltzmannWeightJ G 1 (fun _ => β * J) (β * h) := by
    funext σ'
    rw [boltzmannWeightJ_uniform_eq, boltzmannWeightJ_uniform_eq]
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    congr 1; ring
  unfold boltzmannWeightBC
  rw [hbwJ]

/-- **β-rescaling of the `+` boundary Gibbs expectation**:
`⟨F⟩⁺_{(J,h,β)} = ⟨F⟩⁺_{(βJ,βh,1)}`. -/
theorem gibbsExpectationBC_beta_rescale (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J h : ℝ) (Λ : Finset ι) (η : Config ι) (F : Config ι → ℝ) :
    gibbsExpectationBC G β (fun _ => J) h Λ η F
      = gibbsExpectationBC G 1 (fun _ => β * J) (β * h) Λ η F := by
  unfold gibbsExpectationBC partitionFunctionBC
  simp_rw [boltzmannWeightBC_beta_rescale G β J h Λ η]

omit [Fintype ι] [DecidableEq ι] in
/-- The single-spin observable `σ ↦ σ_x` is monotone. -/
theorem spinProduct_singleton_monotone (x : ι) :
    Monotone (spinProduct ({x} : Finset ι)) := by
  have heq : (spinProduct ({x} : Finset ι)) = fun σ => Spin.sign ℝ (σ x) := by
    funext σ; rw [spinProduct_singleton]; rfl
  rw [heq]; exact singleSpinObs_monotone x

/-- **β-monotonicity of the `+` boundary single-spin correlation**: for `0 < β₁ ≤ β₂`
and a ferromagnetic uniform coupling (`J, h ≥ 0`), `⟨σ_x⟩⁺_Λ` is non-decreasing in
`β`.  Via the rescaling `⟨σ_x⟩⁺_{(J,h,β)} = ⟨σ_x⟩⁺_{(βJ,βh,1)}` plus `J`- and
`h`-monotonicity. -/
theorem gibbsExpectationBC_plus_monotone_beta_singleton (G : SimpleGraph ι)
    [Fintype G.edgeSet] {J h : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset ι) (x : ι)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    gibbsExpectationBC G β₁ (fun _ => J) h Λ (plusConfig ι) (spinProduct {x}) ≤
      gibbsExpectationBC G β₂ (fun _ => J) h Λ (plusConfig ι) (spinProduct {x}) := by
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ
  rw [gibbsExpectationBC_beta_rescale G β₁ J h Λ, gibbsExpectationBC_beta_rescale G β₂ J h Λ]
  calc gibbsExpectationBC G 1 (fun _ => β₁ * J) (β₁ * h) Λ (plusConfig ι) (spinProduct {x})
      ≤ gibbsExpectationBC G 1 (fun _ => β₂ * J) (β₁ * h) Λ (plusConfig ι) (spinProduct {x}) :=
        gibbsExpectationBC_plus_monotone_J G (β₁ * h) (mul_nonneg hβ₁.le hh) 1 one_pos Λ {x}
          (Set.mem_Ici.mpr (mul_nonneg hβ₁.le hJ)) (Set.mem_Ici.mpr (mul_nonneg hβ₂.le hJ))
          (mul_le_mul_of_nonneg_right hβ hJ)
    _ ≤ gibbsExpectationBC G 1 (fun _ => β₂ * J) (β₂ * h) Λ (plusConfig ι) (spinProduct {x}) :=
        gibbsExpectationBC_field_mono G zero_le_one (mul_nonneg hβ₂.le hJ)
          (mul_le_mul_of_nonneg_right hβ hh) Λ (plusConfig ι) (spinProduct {x})
          (spinProduct_singleton_monotone x)

end IsingModel
