import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityInfEnvelopeLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistContinuity

/-!
# GJ §17.5 Theorem 17.5.1 — PR-C: global pseudo-mass-power Lipschitz (conditional capstone)

The GJ p.312 conclusion that the *system* pseudo-mass power `β ↦ (m⁻(β))^{2α+1}` (with
`m⁻ = globalPseudoMassDist`, the infimum over active distinct pairs of the per-pair pseudo-masses)
is Lipschitz on a closed interval, assembled from the lower-envelope fencing lemma
`abs_sub_le_of_isInf_binding_deriv` (PR-A) and the per-binding-pair pointwise derivative bound
`pseudoMassFromParamsAtPairDist_pow_succ_hasDeriv_abs_le_binding` (PR-B1).

**Conditional / Partial.**  Two inputs remain hypotheses (cf. #4320, "transfer-principle-blocked"):

* `hcont` — continuity of the envelope `β ↦ (m⁻(β))^{2α+1}` on the interval (the infimum is only
  upper-semicontinuous a priori; envelope continuity from the per-region infima needs the same
  uniform-in-region constant the chapter's argument supplies but that we have not yet formalized);
* `hbind_deriv` — at every `β` in the interval a globally *binding* active pair exists at which the
  per-pair pseudo-mass power has derivative `≤ M` in absolute value, with `M` uniform in `β` and the
  pair.  Binding-pair existence is `sInf`-over-pairs *attainment*; in the Ornstein--Zernike regime
  the per-pair mass `m_{x,z} ↓ m∞` as `d(x,z) → ∞`, so the infimum is approached but not attained by
  any finite pair.  The uniform bound `M` is the GJ p.312 estimate
  `(2α+1)·S·(m⁻)^{2α}/d(x,z) ≤ M` (bounded for `α ≥ d−1`); PR-B1 supplies the derivative and its
  per-`β` constant, leaving the uniform bound and the binding existence as the genuine gaps.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real Filter

/-- **Global pseudo-mass-power Lipschitz, conditional capstone** (GJ p.312): on `Icc β₁ β₂` inside
the high-temperature window (`0 < β₁`), given (1) continuity `hcont` of the envelope
`β ↦ (m⁻(β))^{2α+1}` and (2) for every `β ∈ Icc` a globally-binding active pair `x ≠ z` at which the
per-pair pseudo-mass power has `|deriv| ≤ M`, the system pseudo-mass power satisfies
`|(m⁻(β₂))^{2α+1} − (m⁻(β₁))^{2α+1}| ≤ M·(β₂ − β₁)`.

Direct application of the lower-envelope fencing lemma `abs_sub_le_of_isInf_binding_deriv` (PR-A):
the family is `f q β = (m⁻(q.1,q.2,β))^{2α+1}` over distinct pairs `q`; domination
`g ≤ f q` is `globalPseudoMassDist_le_of_active` (every distinct pair is active at `β > 0`) raised
to the `(2α+1)` power (`pow_le_pow_left₀`); the binding/derivative data is `hbind_deriv`. -/
theorem globalPseudoMassDist_pow_succ_lipschitz_on_Icc_of_binding_deriv {α d : ℕ} (hα : 1 ≤ α)
    {J β₁ β₂ M : ℝ} (hJ : 0 < J) (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂)
    (hcont : ContinuousOn (fun β => (globalPseudoMassDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)) ^ (2 * α + 1)) (Set.Icc β₁ β₂))
    (hbind_deriv : ∀ β ∈ Set.Icc β₁ β₂, ∃ x z : Fin d → ℤ, x ≠ z ∧
      pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) x z
        = globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      ∃ dv : ℝ, HasDerivAt (fun β' => (pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
          (⟨J, 0, β'⟩ : IsingParams ℝ) x z) ^ (2 * α + 1)) dv β ∧ |dv| ≤ M) :
    |(globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₂⟩ : IsingParams ℝ)) ^ (2 * α + 1)
        - (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β₁⟩ : IsingParams ℝ)) ^ (2 * α + 1)|
      ≤ M * (β₂ - β₁) := by
  classical
  -- index family by *distinct* pairs (diagonal pairs give pseudo-mass `0`, breaking domination).
  set f : {q : (Fin d → ℤ) × (Fin d → ℤ) // q.1 ≠ q.2} → ℝ → ℝ := fun q β =>
    (pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        q.val.1 q.val.2) ^ (2 * α + 1) with hf_def
  set g : ℝ → ℝ := fun β =>
    (globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) ^ (2 * α + 1)
    with hg_def
  -- domination: `g β ≤ f q β` for every distinct pair (all distinct pairs are active at `β > 0`).
  have hle : ∀ q : {q : (Fin d → ℤ) × (Fin d → ℤ) // q.1 ≠ q.2},
      ∀ β ∈ Set.Icc β₁ β₂, g β ≤ f q β := by
    intro q β hβ
    have hβ_pos : 0 < β := lt_of_lt_of_le hβ₁ hβ.1
    have hactive : ActivePseudoMassPair (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        q.val.1 q.val.2 :=
      ⟨q.property, correlationInfinite_pair_active_of_betaJ_pos_exhaustion
        (cubicExhaustion d) hβ_pos (mul_pos hβ_pos hJ) q.val.1 q.val.2 q.property⟩
    have hmass_le : globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            q.val.1 q.val.2 :=
      globalPseudoMassDist_le_of_active hα (cubicExhaustion d) _ hactive
    exact pow_le_pow_left₀ (globalPseudoMassDist_nonneg hα _ _) hmass_le _
  -- binding data.
  have hbind : ∀ β ∈ Set.Icc β₁ β₂,
      ∃ q : {q : (Fin d → ℤ) × (Fin d → ℤ) // q.1 ≠ q.2}, g β = f q β ∧
      ∃ dv : ℝ, HasDerivAt (f q) dv β ∧ |dv| ≤ M := by
    intro β hβ
    obtain ⟨x, z, hxz, hbindeq, dv, hderiv, hdvM⟩ := hbind_deriv β hβ
    refine ⟨⟨(x, z), hxz⟩, ?_, dv, ?_, hdvM⟩
    · simp only [hf_def, hg_def]
      rw [hbindeq]
    · simpa only [hf_def] using hderiv
  simpa [hg_def] using abs_sub_le_of_isInf_binding_deriv hβ₁₂ hcont hle hbind

end Ambient
end IsingModel
