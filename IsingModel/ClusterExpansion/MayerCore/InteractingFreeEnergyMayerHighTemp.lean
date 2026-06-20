import IsingModel.ClusterExpansion.MayerCore.InteractingFreeEnergyMayer
import IsingModel.ClusterExpansion.MayerCore.MayerTanhConvergence

/-!
# High-temperature discharge of the interacting Mayer expansion (GJ §18.5)

The two Mayer--Montroll convergence hypotheses of
`freeEnergy_eq_tsum_mayer_of_activity` are discharged from explicit
high-temperature smallness conditions on the finite graph:

* the log-convergence condition `|ε(t)| < 1` follows from `(1 + t)^|E| < 2`
  (with `t = tanh(βJ) ≥ 0`), since `0 ≤ ε(t) ≤ (1+t)^|E| − 1`;
* the activity condition `e·∑_P |t|^|P| < 1` follows from
  `e·|allPolymers G|·tanh(βJ) < 1`, since
  `∑_P tanh(βJ)^|P| ≤ |allPolymers G|·tanh(βJ)`.

Both right-hand conditions tend to the trivially satisfied limit as `βJ → 0`
(`tanh(βJ) → 0`), so this is the genuine high-temperature regime.  The result is
the interacting Ising free energy expressed as its convergent cluster expansion
under explicit finite-graph high-temperature conditions, with no separate
convergence hypotheses.

This remains a finite-volume statement; the volume-uniform / infinite-volume
analyticity of the pressure is later work.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386 (the
  cluster-expansion convergence mechanism for the pressure / free energy).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Mayer log-convergence condition `|ε(t)| < 1` from `(1+t)^|E| < 2` (for
`t ≥ 0`). -/
theorem mayer_log_condition_of_one_add_pow_lt_two
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht : 0 ≤ t)
    (hpow : (1 + t) ^ G.edgeFinset.card < 2) :
    |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card| < 1 := by
  have h0 := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have hle := vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht
  rw [abs_of_nonneg h0]
  linarith

omit [Fintype ι] in
/-- The Mayer activity condition at `t = tanh(βJ)` from
`e·|allPolymers G|·tanh(βJ) < 1` (for `0 ≤ βJ`). -/
theorem mayer_activity_condition_tanh_of_card_mul_lt
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hcard : Real.exp 1 * ((allPolymers G).card * Real.tanh (β * J)) < 1) :
    Real.exp 1 * (∑ P ∈ allPolymers G, |Real.tanh (β * J)| ^ P.card) < 1 := by
  have hsum := tanh_activity_sum_le_card_mul_tanh G hβJ
  have habs : (∑ P ∈ allPolymers G, |Real.tanh (β * J)| ^ P.card)
      = ∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card := by
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [abs_of_nonneg (real_tanh_nonneg hβJ)]
  rw [habs]
  calc Real.exp 1 * (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card)
      ≤ Real.exp 1 * ((allPolymers G).card * Real.tanh (β * J)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos 1).le
    _ < 1 := hcard

/-- **High-temperature interacting Ising free energy as a Mayer expansion**
(GJ §18.5).  Under the explicit finite-graph high-temperature conditions
`(1 + tanh βJ)^|E| < 2` and `e·|allPolymers G|·tanh(βJ) < 1` (and `0 ≤ βJ`,
`0 < |ι|`), the Ising free energy at zero field equals its convergent cluster
expansion, with no separate convergence hypotheses. -/
theorem freeEnergy_eq_tsum_mayer_of_high_temp
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι)
    (hht : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2 ∧
      Real.exp 1 * ((allPolymers G).card * Real.tanh (β * J)) < 1) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι :=
  freeEnergy_eq_tsum_mayer_of_activity G J β hβJ hne
    (mayer_log_condition_of_one_add_pow_lt_two G (real_tanh_nonneg hβJ) hht.1)
    (mayer_activity_condition_tanh_of_card_mul_lt G hβJ hht.2)

/-- **Ferromagnetic high-temperature form** (GJ §18.5): hypotheses `0 ≤ J`,
`0 < β`. -/
theorem freeEnergy_eq_tsum_mayer_of_high_temp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (hht : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2 ∧
      Real.exp 1 * ((allPolymers G).card * Real.tanh (β * J)) < 1) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J)) +
        (∑' n, mayerExpansionTerm G n (Real.tanh (β * J))) / Fintype.card ι :=
  freeEnergy_eq_tsum_mayer_of_high_temp G J β (mul_nonneg hβ.le hJ) hne hht

end IsingModel
