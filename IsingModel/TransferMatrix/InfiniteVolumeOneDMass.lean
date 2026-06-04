import IsingModel.TransferMatrix.InfiniteVolumeOneDSusceptibility
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncated2EqSubMagSq
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMagCorrelationTrivialTrivialSlices
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation

/-!
# Sharp 1D lattice mass and cluster property (Glimm–Jaffe §17.1, §17.5)

The exact infinite-volume two-point identity of the one-dimensional Ising chain,
`twoPointFunction 1 ⟨J,0,β⟩ r = (tanh βJ)^|r| = exp(−m·|r|)` with mass
`m = correlationMass (βJ) = −log tanh βJ` (`twoPointFunction_one_eq_tanh_pow`
/`twoPointFunction_one_eq_exp_neg_mass`, #3535/#3536), pins down the abstract
§17.5 **lattice mass** `latticeMass 1 (cubicExhaustion 1) ⟨J,0,β⟩` — the
supremum of admissible exponential-decay rates of the truncated two-point
function — *exactly*:

  `latticeMass 1 (cubicExhaustion 1) ⟨J,0,β⟩ = ENNReal.ofReal (correlationMass βJ)`.

At zero external field the spontaneous magnetization vanishes
(`magnetizationInfinite_latticeGraph_zero_at_h_zero`), so the truncated (Ursell)
two-point function coincides with the full two-point function; by translation
invariance the truncated function at any distinct pair `(i, j)` equals the exact
geometric value `(tanh βJ)^{dist(i,j)}`.  Exponential decay then holds with
constant `C = 1` at the mass rate `m`, giving `m ≤ latticeMass`; and no rate
`α > m` can work, since the *exact* value `exp(−m·n)` forces
`exp((α − m)·n) ≤ C` for all `n`, impossible.  Positivity of `m` yields the
infinite-volume cluster property.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1, §17.5, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

open Filter Topology

/-- **Translation of the `ℓ¹` lattice distance to the origin**:
`latticeDistance d 0 (j − i) = latticeDistance d i j`.  Each summand
`|0 − (j k − i k)| = |i k − j k|` by `Int.natAbs_sub_comm`. -/
lemma latticeDistance_zero_sub (d : ℕ) (i j : Fin d → ℤ) :
    latticeDistance d 0 (j - i) = latticeDistance d i j := by
  unfold latticeDistance
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, Int.natAbs_neg]
  omega

/-- **Exact truncated two-point function of the 1D chain (tanh form)**:
for `J ≥ 0`, `β > 0` and distinct `i, j : Fin 1 → ℤ`,

`truncated2Infinite (latticeGraph 1) (cubicExhaustion 1) ⟨J,0,β⟩ i j
  = (tanh βJ)^{latticeDistance 1 i j}`.

At `h = 0` the spontaneous magnetization vanishes, so the truncated (Ursell)
two-point function equals the full two-point function, which by translation
invariance is the exact geometric value (GJ §17.1, #3535). -/
theorem truncated2Infinite_one_eq_tanh_pow {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {i j : Fin 1 → ℤ} (hij : i ≠ j) :
    Ambient.truncated2Infinite (IsingModel.latticeGraph 1)
        (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = Real.tanh (β * J) ^ latticeDistance 1 i j := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hr0 : (j - i) 0 ≠ 0 := by
    rw [Pi.sub_apply, sub_ne_zero]
    intro h
    apply hij
    funext k
    fin_cases k
    exact h.symm
  rw [Ambient.truncated2Infinite_latticeGraph_cubicExhaustion_eq_twoPoint 1 _ hf i j,
    Ambient.truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq 1 _ hf (j - i),
    Ambient.magnetizationInfinite_latticeGraph_zero_at_h_zero 1 _ J β 0,
    twoPointFunction_one_eq_tanh_pow hJ hβ (j - i) hr0, latticeDistance_zero_sub 1 i j]
  ring

/-- **Exact truncated two-point function of the 1D chain (mass form)**:
for `J ≥ 0`, `β > 0`, `βJ > 0` and distinct `i, j : Fin 1 → ℤ`,

`truncated2Infinite (latticeGraph 1) (cubicExhaustion 1) ⟨J,0,β⟩ i j
  = exp(−m · latticeDistance 1 i j)`   with mass `m = correlationMass (βJ)`. -/
theorem truncated2Infinite_one_eq_exp_neg_mass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) {i j : Fin 1 → ℤ} (hij : i ≠ j) :
    Ambient.truncated2Infinite (IsingModel.latticeGraph 1)
        (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = Real.exp (-(correlationMass (β * J)) * (latticeDistance 1 i j : ℝ)) := by
  rw [truncated2Infinite_one_eq_tanh_pow hJ hβ hij, tanh_pow_eq_exp_neg_mass hβJ]

/-- **Truncated two-point at the origin equals the full two-point function**
(`h = 0`): for `J ≥ 0`, `β > 0` and any `r : Fin 1 → ℤ`,

`truncated2Infinite (latticeGraph 1) (cubicExhaustion 1) ⟨J,0,β⟩ 0 r
  = twoPointFunction 1 ⟨J,0,β⟩ r`.

The spontaneous magnetization vanishes at zero field, so the connected piece
`G(r) − M(0)²` reduces to `G(r)`.  Holds for every `r` (including `r = 0`). -/
theorem truncated2Infinite_one_zero_eq_twoPointFunction {J β : ℝ} (hJ : 0 ≤ J)
    (hβ : 0 < β) (r : Fin 1 → ℤ) :
    Ambient.truncated2Infinite (IsingModel.latticeGraph 1)
        (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) 0 r
      = Ambient.twoPointFunction 1 (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  rw [Ambient.truncated2Infinite_latticeGraph_cubicExhaustion_eq_twoPoint 1 _ hf 0 r,
    Ambient.truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq 1 _ hf (r - 0),
    Ambient.magnetizationInfinite_latticeGraph_zero_at_h_zero 1 _ J β 0]
  simp

/-- **Exponential decay at the exact 1D mass** (GJ §17.5): for `J ≥ 0`, `β > 0`
and `βJ > 0`,

`HasExponentialDecay 1 (cubicExhaustion 1) ⟨J,0,β⟩ (correlationMass βJ)`,

witnessed by the constant `C = 1` and the exact geometric value of the truncated
two-point function. -/
theorem HasExponentialDecay_one_correlationMass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) :
    Ambient.HasExponentialDecay 1 (Ambient.cubicExhaustion 1)
      (⟨J, 0, β⟩ : IsingParams ℝ) (correlationMass (β * J)) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro i j hij
  rw [truncated2Infinite_one_eq_exp_neg_mass hJ hβ hβJ hij, abs_of_pos (Real.exp_pos _),
    one_mul]

/-- **Lower bound on the lattice mass** (GJ §17.5): the exact 1D mass realises an
admissible exponential-decay rate, so

`ENNReal.ofReal (correlationMass βJ) ≤ latticeMass 1 (cubicExhaustion 1) ⟨J,0,β⟩`. -/
theorem latticeMass_one_ge_correlationMass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) :
    ENNReal.ofReal (correlationMass (β * J))
      ≤ Ambient.latticeMass 1 (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) :=
  Ambient.latticeMass_ge_of_HasExponentialDecay (le_of_lt (correlationMass_pos hβJ))
    (HasExponentialDecay_one_correlationMass hJ hβ hβJ)

/-- **No decay faster than the exact 1D mass** (GJ §17.5): any admissible
exponential-decay rate `α` for the 1D chain is bounded by the exact mass,

`HasExponentialDecay 1 (cubicExhaustion 1) ⟨J,0,β⟩ α → α ≤ correlationMass βJ`.

If `α > m`, applying the decay bound at the points `0` and `(n, …)` (distance
`n`) and the *exact* value `exp(−m·n)` gives `exp((α − m)·n) ≤ C` for all `n`,
contradicting `exp((α − m)·n) → ∞`. -/
theorem le_correlationMass_of_HasExponentialDecay {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) {α : ℝ}
    (h : Ambient.HasExponentialDecay 1 (Ambient.cubicExhaustion 1)
      (⟨J, 0, β⟩ : IsingParams ℝ) α) :
    α ≤ correlationMass (β * J) := by
  obtain ⟨C, hC, hbound⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  set m := correlationMass (β * J) with hm
  set δ := α - m with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set pt : ℕ → (Fin 1 → ℤ) := fun n => (fun _ => (n : ℤ)) with hpt
  have hdist : ∀ n : ℕ, latticeDistance 1 (0 : Fin 1 → ℤ) (pt n) = n := by
    intro n
    simp only [latticeDistance, Fin.sum_univ_one, Pi.zero_apply, hpt, zero_sub,
      Int.natAbs_neg, Int.natAbs_natCast]
  have hne : ∀ n : ℕ, 1 ≤ n → (0 : Fin 1 → ℤ) ≠ pt n := by
    intro n hn hcontra
    have h0 : (pt n) 0 = 0 := by rw [← hcontra]; rfl
    simp only [hpt] at h0
    omega
  have hboundn : ∀ n : ℕ, 1 ≤ n → Real.exp (δ * (n : ℝ)) ≤ C := by
    intro n hn
    have hb := hbound 0 (pt n) (hne n hn)
    rw [truncated2Infinite_one_eq_exp_neg_mass hJ hβ hβJ (hne n hn), hdist n,
      abs_of_pos (Real.exp_pos _)] at hb
    -- hb : exp(-m·n) ≤ C * exp(-α·n)
    have hαexp : 0 < Real.exp (-α * (n : ℝ)) := Real.exp_pos _
    have hkey : Real.exp (δ * (n : ℝ)) * Real.exp (-α * (n : ℝ))
        = Real.exp (-m * (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; rw [hδdef]; ring
    have heq : Real.exp (δ * (n : ℝ))
        = Real.exp (-m * (n : ℝ)) / Real.exp (-α * (n : ℝ)) :=
      eq_div_of_mul_eq (ne_of_gt hαexp) hkey
    rw [heq, div_le_iff₀ hαexp]
    exact hb
  have hlin : Tendsto (fun n : ℕ => δ * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : ℕ => Real.exp (δ * (n : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  obtain ⟨n, hgt, hge⟩ :=
    ((htend.eventually_gt_atTop C).and (eventually_ge_atTop 1)).exists
  exact absurd (hboundn n hge) (not_le.mpr hgt)

/-- **Upper bound on the lattice mass** (GJ §17.5): no admissible rate exceeds the
exact 1D mass, so

`latticeMass 1 (cubicExhaustion 1) ⟨J,0,β⟩ ≤ ENNReal.ofReal (correlationMass βJ)`. -/
theorem latticeMass_one_le_correlationMass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) :
    Ambient.latticeMass 1 (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (correlationMass (β * J)) := by
  unfold Ambient.latticeMass
  apply sSup_le
  rintro x ⟨αNN, hdecay, rfl⟩
  have hle : (αNN : ℝ) ≤ correlationMass (β * J) :=
    le_correlationMass_of_HasExponentialDecay hJ hβ hβJ hdecay
  calc ((fun α : NNReal => (α : ENNReal)) αNN)
      = ENNReal.ofReal (αNN : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (correlationMass (β * J)) := ENNReal.ofReal_le_ofReal hle

/-- **Sharp 1D lattice mass** (Glimm–Jaffe §17.5): the abstract supremal
exponential-decay rate of the truncated two-point function equals the exact
transfer-matrix mass,

`latticeMass 1 (cubicExhaustion 1) ⟨J,0,β⟩ = ENNReal.ofReal (correlationMass βJ)`,

for `J ≥ 0`, `β > 0`, `βJ > 0`.  The §17.5 mass is realised and sharp in one
dimension. -/
theorem latticeMass_one_eq_correlationMass {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) :
    Ambient.latticeMass 1 (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ)
      = ENNReal.ofReal (correlationMass (β * J)) :=
  le_antisymm (latticeMass_one_le_correlationMass hJ hβ hβJ)
    (latticeMass_one_ge_correlationMass hJ hβ hβJ)

/-- **Sharp 1D lattice mass in terms of the correlation length** (GJ §17.5):
`latticeMass = ofReal (1 / ξ)` with `ξ = correlationLength (βJ)`, the physical
inverse-correlation-length reading of the mass. -/
theorem latticeMass_one_eq_ofReal_inv_correlationLength {J β : ℝ} (hJ : 0 ≤ J)
    (hβ : 0 < β) (hβJ : 0 < β * J) :
    Ambient.latticeMass 1 (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ)
      = ENNReal.ofReal (1 / correlationLength (β * J)) := by
  rw [latticeMass_one_eq_correlationMass hJ hβ hβJ, correlationMass_eq_inv_length]

/-- **Infinite-volume cluster property of the 1D chain** (Glimm–Jaffe §5.1, §17.5):
for `J ≥ 0`, `β > 0`, `βJ > 0` the truncated two-point function tends to `0`
along the cofinite filter, derived from positive-mass exponential decay. -/
theorem clusterProperty_one {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ : 0 < β * J) :
    Ambient.clusterProperty (IsingModel.latticeGraph 1) (Ambient.cubicExhaustion 1)
      (⟨J, 0, β⟩ : IsingParams ℝ) :=
  Ambient.clusterProperty_latticeGraph_of_HasExponentialDecay 1
    (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) (correlationMass_pos hβJ)
    (HasExponentialDecay_one_correlationMass hJ hβ hβJ)

/-- **Decay of the infinite-volume two-point function** (GJ §17.1, §5.1): for
`J ≥ 0`, `β > 0`, `βJ > 0`,

`twoPointFunction 1 ⟨J,0,β⟩ r → 0`   along the cofinite filter in `r`.

At zero field the full two-point function equals the truncated one, so the
cluster property transfers directly. -/
theorem twoPointFunction_one_tendsto_cofinite_zero {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hβJ : 0 < β * J) :
    Filter.Tendsto
      (fun r : Fin 1 → ℤ => Ambient.twoPointFunction 1 (⟨J, 0, β⟩ : IsingParams ℝ) r)
      Filter.cofinite (nhds 0) :=
  (clusterProperty_one hJ hβ hβJ 0).congr
    (fun r => truncated2Infinite_one_zero_eq_twoPointFunction hJ hβ r)

end TransferMatrix

end IsingModel
