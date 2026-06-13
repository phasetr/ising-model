import IsingModel.ContinuousSpin.TwoComponentRotationAlgebra

/-!
# The doubled Gibbs weight factorises through the block rotation (GJ Thm 4.7.1)

The pointwise weight identity at the heart of the duplicate-variable proof of the
second/third inequalities (4.7.6)–(4.7.8).  Writing `cfg i = rotLin (dCoord ξ ξ' i)`
for the §4.7 block rotation of the doubled configuration `(ξ, ξ')`, the product
of the two single-copy Gibbs weights is the doubled-rotated weight:
`W(ξ)·W(ξ') = exp(βJ·∑_e edgeDot4 cfg e) · ∏ᵢ siteWeight4 A σ (√2βh¹) (√2βh²) (cfg i)`
(`vectorWeight_mul_eq_rot`).

This combines:
* the interaction identity (GJ (4.3.5)) `∑_e (ξ·ξ + ξ'·ξ') = ∑_e edgeDot4 cfg`;
* the field identity `βh¹(tᵢ+tᵢ') + βh²(qᵢ+qᵢ') = √2βh¹·αᵢ + √2βh²·γᵢ`;
* the potential identity `P(ξ) + P(ξ') = twoCompEvenPart − 4A·αβγδ`.

The doubled field constants `√2βh¹, √2βh² ≥ 0` (for `β, h¹, h² ≥ 0`) are exactly
the non-negative field hypotheses of `dRotInteraction_nonneg`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, pp. 70–71
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

variable {ι : Type*}

/-- The per-edge interaction identity (GJ (4.3.5)) lifted to `Sym2 ι`:
`ξᵢ·ξⱼ + ξᵢ'·ξⱼ' = edgeDot4 cfg` for the block-rotated configuration. -/
theorem doubled_vEdgeDot_eq_edgeDot4 (ξ ξ' : VectorConfig ι) (e : Sym2 ι) :
    vEdgeDot ξ e + vEdgeDot ξ' e = edgeDot4 (fun i => rotLin (dCoord ξ ξ' i)) e := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [vEdgeDot, edgeDot4, Sym2.lift_mk]
    exact doubled_dot_eq_rot ξ ξ' i j

/-- The defining product `√2 · (√2/2) = 1`. -/
theorem sqrt2_mul_sqrt2_half : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
  rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- **The per-site doubled exponent identity**: the field-minus-potential exponent of
the two single-copy weights at a site equals the field-minus-even-plus-cross exponent
of the doubled-rotated per-site weight. -/
theorem doubled_site_exponent (A σ h1 h2 β ti qi ti' qi' : ℝ) :
    β * h1 * ti + β * h2 * qi + β * h1 * ti' + β * h2 * qi'
        - (twoCompPotential A σ ti qi + twoCompPotential A σ ti' qi')
      = Real.sqrt 2 * β * h1 * bAlpha ti ti' + Real.sqrt 2 * β * h2 * bGamma qi qi'
        - twoCompEvenPart A σ (bAlpha ti ti') (bBeta ti ti') (bGamma qi qi') (bDelta qi qi')
        + 4 * A * (bAlpha ti ti' * bBeta ti ti' * bGamma qi qi' * bDelta qi qi') := by
  have hfield : Real.sqrt 2 * β * h1 * bAlpha ti ti' + Real.sqrt 2 * β * h2 * bGamma qi qi'
      = β * h1 * ti + β * h2 * qi + β * h1 * ti' + β * h2 * qi' := by
    simp only [bAlpha, bGamma]
    linear_combination (β * h1 * (ti + ti') + β * h2 * (qi + qi')) * sqrt2_mul_sqrt2_half
  rw [twoCompPotential_double_block]
  linarith [hfield]

/-- **The doubled Gibbs weight factorises through the block rotation** (GJ Thm 4.7.1):
`W(ξ)·W(ξ') = exp(βJ·∑_e edgeDot4 cfg) · ∏ᵢ siteWeight4 A σ (√2βh¹) (√2βh²) (cfg i)`,
with `cfg i = rotLin (dCoord ξ ξ' i)`.  This is the weight side of the
duplicate-variable change of variables for the second/third inequalities. -/
theorem vectorWeight_mul_eq_rot [Fintype ι] (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) (ξ ξ' : VectorConfig ι) :
    vectorWeight G A σ J h1 h2 β ξ * vectorWeight G A σ J h1 h2 β ξ'
      = Real.exp (β * J * ∑ e ∈ G.edgeFinset, edgeDot4 (fun i => rotLin (dCoord ξ ξ' i)) e)
        * ∏ i, siteWeight4 A σ (Real.sqrt 2 * β * h1) (Real.sqrt 2 * β * h2)
            (rotLin (dCoord ξ ξ' i)) := by
  set cfg : ι → Fin 4 → ℝ := fun i => rotLin (dCoord ξ ξ' i) with hcfg
  -- block coordinates of each site
  have hc0 : ∀ i, cfg i 0 = bAlpha (ξ i).1 (ξ' i).1 := fun i => (rotLin_dCoord ξ ξ' i).1
  have hc1 : ∀ i, cfg i 1 = bBeta (ξ i).1 (ξ' i).1 := fun i => (rotLin_dCoord ξ ξ' i).2.1
  have hc2 : ∀ i, cfg i 2 = bGamma (ξ i).2 (ξ' i).2 := fun i => (rotLin_dCoord ξ ξ' i).2.2.1
  have hc3 : ∀ i, cfg i 3 = bDelta (ξ i).2 (ξ' i).2 := fun i => (rotLin_dCoord ξ ξ' i).2.2.2
  -- rewrite the RHS product as a single exponential
  have hfac : ∀ i, siteWeight4 A σ (Real.sqrt 2 * β * h1) (Real.sqrt 2 * β * h2) (cfg i)
      = Real.exp (Real.sqrt 2 * β * h1 * cfg i 0 + Real.sqrt 2 * β * h2 * cfg i 2
          + (-twoCompEvenPart A σ (cfg i 0) (cfg i 1) (cfg i 2) (cfg i 3)
            + 4 * A * (cfg i 0 * cfg i 1 * cfg i 2 * cfg i 3))) := by
    intro i; rw [siteWeight4, rotSiteDensity, ← Real.exp_add]
  have hprod : ∏ i, siteWeight4 A σ (Real.sqrt 2 * β * h1) (Real.sqrt 2 * β * h2) (cfg i)
      = Real.exp (∑ i, (Real.sqrt 2 * β * h1 * cfg i 0 + Real.sqrt 2 * β * h2 * cfg i 2
          + (-twoCompEvenPart A σ (cfg i 0) (cfg i 1) (cfg i 2) (cfg i 3)
            + 4 * A * (cfg i 0 * cfg i 1 * cfg i 2 * cfg i 3)))) := by
    rw [Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]
  rw [hprod, ← Real.exp_add]
  rw [vectorWeight, vectorWeight, ← Real.exp_add]
  congr 1
  -- reduce to the exponent identity
  rw [vectorHamiltonian, vectorHamiltonian, vectorPotentialSum, vectorPotentialSum]
  -- edge part
  have hedge : β * J * ∑ e ∈ G.edgeFinset, edgeDot4 cfg e
      = β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e + β * J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ' e := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
    rw [← doubled_vEdgeDot_eq_edgeDot4]
  -- site part: rewrite the doubled-rotated site sum into the original spin sum
  have hsite : ∑ i, (Real.sqrt 2 * β * h1 * cfg i 0 + Real.sqrt 2 * β * h2 * cfg i 2
        + (-twoCompEvenPart A σ (cfg i 0) (cfg i 1) (cfg i 2) (cfg i 3)
          + 4 * A * (cfg i 0 * cfg i 1 * cfg i 2 * cfg i 3)))
      = ∑ i, (β * h1 * vSpinT ξ i + β * h2 * vSpinQ ξ i
            + β * h1 * vSpinT ξ' i + β * h2 * vSpinQ ξ' i
          - (twoCompPotential A σ (vSpinT ξ i) (vSpinQ ξ i)
            + twoCompPotential A σ (vSpinT ξ' i) (vSpinQ ξ' i))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc0, hc1, hc2, hc3]
    simp only [vSpinT, vSpinQ]
    linear_combination
      (doubled_site_exponent A σ h1 h2 β (ξ i).1 (ξ i).2 (ξ' i).1 (ξ' i).2).symm
  rw [hedge, hsite]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end IsingModel.ContinuousSpin
