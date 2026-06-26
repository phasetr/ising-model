import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTemperature.UpperBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeUnconditional

/-!
# GJ §17.5 Lemma 17.5.2 — tractable restricted upper bound and faithful sandwich

This module supplies the **tractable restricted upper bound** of Glimm--Jaffe
§17.5 Lemma 17.5.2 against the distance-parametrized system pseudo-mass
`globalPseudoMassDist`.  Combined with the (already merged) faithful lower bound
`globalPseudoMassDist_le_latticeMass`, it produces the two-sided sandwich
`m⁻(σ) ≤ m(σ) ≤ C · m⁻(σ)` on the strict high-temperature window of the cubic
exhaustion, both sides phrased against `globalPseudoMassDist`.

The *full* high-temperature (`βJ·2d < 1`) / arbitrary-exhaustion upper bound
`m(σ) ≤ C · m⁻(σ)` needs a *pair-uniform full-window correlation-decay*
(uniform Hardy--Littlewood--Sobolev) constant — the book obtains it from the
transfer matrix, the route whose §17.1 spectral form is obstructed (#4081 is
that related obstruction, not literally the single missing lemma here). So we
target the **tractable restricted** version available from unconditional
inputs:

* the high-temperature lattice-mass ceiling
  `latticeMass ≤ ENNReal.ofReal (−log(tanh(βJ)))`
  (`latticeMass_le_neg_log_tanh_betaJ`);
* the unconditional pseudo-mass-to-lattice-distance bridge
  `pseudoMassLatticeDistanceBridge_of_high_temp` built from the Simon--Lieb
  trichotomy plus the susceptibility-ceiling adjacent input, whose pair-uniform
  rate `M = min (min 1 (−log B)) (simonLiebRate /(2(α+1)))`
  (with `B = βJ·2d/(1−βJ·2d)`) is **independent of the profile radius**.

Aligning the bridge's profile radius with each pair's ℓ¹ lattice distance turns
its per-pair bound into a pair-uniform lower bound on the distance-parametrized
per-pair pseudo-mass, hence (by the infimum) on `globalPseudoMassDist`.  Dividing
the lattice-mass ceiling by that rate gives the restricted upper constant
`C = (−log(tanh(βJ))) / M`.

The forced window is `1 ≤ α`, `0 < d`, `0 < J`, `0 < β`, and `β·J·(2d) < 1/2`
(no `d < 2α` is needed: the restricted upper bound does not use the HLS
pair-product sum, only the pair-uniform pseudo-mass lower bound).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312;
  §5.1, pp.~73--74.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **Restricted high-temperature lower rate for the distance-parametrized
pseudo-mass**.

This is exactly the pair-uniform rate
`M = min (min 1 (−log B)) (simonLiebRate β J d / (2(α+1)))`,
with `B = βJ·2d/(1−βJ·2d)`, used inside the unconditional bridge
`pseudoMassLatticeDistanceBridge_of_high_temp`.  In the strict window
`0 < βJ·2d < 1/2` it is strictly positive and serves as a single, pair-uniform
lower bound for every active distinct pair's pseudo-mass.

References: Glimm--Jaffe §17.5, pp.~311--312. -/
noncomputable def globalPseudoMassDistRestrictedRate (α d : ℕ) (J β : ℝ) : ℝ :=
  min (min 1 (-Real.log (β * J * (2 * d) / (1 - β * J * (2 * d)))))
    (simonLiebRate β J d / (2 * ((α : ℝ) + 1)))

/-- **Positivity of the restricted pseudo-mass rate in the strict window**:
for `0 < βJ·2d < 1/2`, the rate
`globalPseudoMassDistRestrictedRate α d J β` is strictly positive.

In this window `B = βJ·2d/(1−βJ·2d) ∈ (0,1)`, so `−log B > 0`; combined with
`simonLiebRate > 0` and `1 > 0`, the three-fold minimum is positive. -/
theorem globalPseudoMassDistRestrictedRate_pos
    {α d : ℕ} {J β : ℝ}
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_half : β * J * (2 * d) < 1 / 2) :
    0 < globalPseudoMassDistRestrictedRate α d J β := by
  have hβJd_lt1 : β * J * (2 * d) < 1 := by linarith
  have hden_pos : 0 < 1 - β * J * (2 * d) := by linarith
  have hB_pos : 0 < β * J * (2 * d) / (1 - β * J * (2 * d)) :=
    div_pos hβJd_pos hden_pos
  have hB_lt1 : β * J * (2 * d) / (1 - β * J * (2 * d)) < 1 := by
    rw [div_lt_one hden_pos]; linarith
  have hnlogB_pos :
      0 < -Real.log (β * J * (2 * d) / (1 - β * J * (2 * d))) := by
    have := Real.log_neg hB_pos hB_lt1; linarith
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hSLfrac_pos : 0 < simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by positivity
  unfold globalPseudoMassDistRestrictedRate
  exact lt_min (lt_min one_pos hnlogB_pos) hSLfrac_pos

/-- **Pair-uniform lower bound on the distance-parametrized per-pair
pseudo-mass**: for every distinct pair `x ≠ z` in the strict high-temperature
window, the restricted rate bounds the distance-parametrized per-pair
pseudo-mass `pseudoMassFromParamsAtPairDist`.

The unconditional bridge `pseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent`
is instantiated at the profile radius `r = latticeDistance d x z` and the
explicit rate `M = globalPseudoMassDistRestrictedRate α d J β`; its per-pair
bound `M · dist ≤ pseudoMassFromParamsAtPair · dist` is divided by `0 < dist`,
and `pseudoMassFromParamsAtPair` at radius `dist` coincides with
`pseudoMassFromParamsAtPairDist` (proof-irrelevant radius). -/
theorem globalPseudoMassDistRestrictedRate_le_pseudoMassFromParamsAtPairDist
    {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_half : β * J * (2 * d) < 1 / 2)
    {x z : Fin d → ℤ} (hxz : x ≠ z) :
    globalPseudoMassDistRestrictedRate α d J β ≤
      pseudoMassFromParamsAtPairDist hα (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  -- Profile radius `dist := latticeDistance d x z` is positive on a distinct pair.
  have hdist : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    have hne : IsingModel.latticeDistance d x z ≠ 0 :=
      fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- Scalar preparation for the rate `M`.
  have hβJd_lt1 : β * J * (2 * d) < 1 := by linarith
  have hden_pos : 0 < 1 - β * J * (2 * d) := by linarith
  have hB_pos : 0 < β * J * (2 * d) / (1 - β * J * (2 * d)) :=
    div_pos hβJd_pos hden_pos
  have hB_lt1 : β * J * (2 * d) / (1 - β * J * (2 * d)) < 1 := by
    rw [div_lt_one hden_pos]; linarith
  have hSL_pos : 0 < simonLiebRate β J d := simonLiebRate_pos hβJd_pos hβJd_lt1
  have hαR_pos : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hM_pos : 0 < globalPseudoMassDistRestrictedRate α d J β :=
    globalPseudoMassDistRestrictedRate_pos hβJd_pos hβJd_half
  have hM_le1 : globalPseudoMassDistRestrictedRate α d J β ≤ 1 := by
    unfold globalPseudoMassDistRestrictedRate
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hM_le_nlogB :
      globalPseudoMassDistRestrictedRate α d J β
        ≤ -Real.log (β * J * (2 * d) / (1 - β * J * (2 * d))) := by
    unfold globalPseudoMassDistRestrictedRate
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hM_le_SLfrac :
      globalPseudoMassDistRestrictedRate α d J β
        ≤ simonLiebRate β J d / (2 * ((α : ℝ) + 1)) := by
    unfold globalPseudoMassDistRestrictedRate
    exact min_le_right _ _
  have hMrate_sl :
      ((α : ℝ) + 1) * globalPseudoMassDistRestrictedRate α d J β
        ≤ simonLiebRate β J d / 2 := by
    calc ((α : ℝ) + 1) * globalPseudoMassDistRestrictedRate α d J β
        ≤ ((α : ℝ) + 1) * (simonLiebRate β J d / (2 * ((α : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hM_le_SLfrac (le_of_lt hαR_pos)
      _ = simonLiebRate β J d / 2 := by field_simp
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- Build the bridge at radius `dist` with `M_inf` set to the restricted rate.
  have hbound :
      globalPseudoMassDistRestrictedRate α d J β
          * (IsingModel.latticeDistance d x z : ℝ) ≤
        pseudoMassFromParamsAtPair hα hdist d (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x z
          * (IsingModel.latticeDistance d x z : ℝ) :=
    (PseudoMassLatticeDistanceBridge_of_simonLieb_trichotomy_adjacent
        hα hdist d hJ hβ hβJ_pos hβJd_pos (le_of_lt hβJd_lt1)
        hM_pos hM_le1 hMrate_sl
        (fun w _ =>
          correlationInfinite_latticeGraph_pair_le_exp_neg_of_high_temp hf
            hβJd_pos hβJd_half hM_le_nlogB w)).bound x z hxz
  have hcancel :
      globalPseudoMassDistRestrictedRate α d J β ≤
        pseudoMassFromParamsAtPair hα hdist d (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    le_of_mul_le_mul_right hbound hdist
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hxz hdist]
  exact hcancel

/-- **Nonemptiness of the distance-pseudo-mass value set in positive
dimension**: in dimension `d ≥ 1` with `0 < β` and `0 < β·J`, the active
distinct pair `(0, e₀)` (where `e₀` is the first unit lattice vector) witnesses a
nonempty `globalPseudoMassDistSet`.

The coordinate `e₀ = Pi.single ⟨0, hd⟩ 1` differs from `0`, and
`correlationInfinite_pair_active_of_betaJ_pos` places its correlation in the
active window `Ioo 0 2`. -/
theorem globalPseudoMassDistSet_nonempty_of_high_temp
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hβ : 0 < β) (hβJ_pos : 0 < β * J) :
    (globalPseudoMassDistSet hα (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ)).Nonempty := by
  classical
  let e₀ : Fin d → ℤ := Pi.single ⟨0, hd⟩ 1
  have h0e : (0 : Fin d → ℤ) ≠ e₀ := by
    intro h
    have hval := congrFun h ⟨0, hd⟩
    simp [e₀] at hval
  have hactive :
      ActivePseudoMassPair (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) 0 e₀ :=
    ⟨h0e, correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos 0 e₀ h0e⟩
  exact ⟨_, 0, e₀, hactive, rfl⟩

/-- **Pair-uniform lower bound for the distance-parametrized system
pseudo-mass**: in the strict high-temperature window of the cubic exhaustion, the
restricted rate bounds `globalPseudoMassDist` from below.

The infimum defining `globalPseudoMassDist` is over a nonempty, bounded-below set
(`globalPseudoMassDistSet_nonempty_of_high_temp`,
`globalPseudoMassDistSet_bddBelow`); `le_csInf` reduces the claim to the
per-active-pair bound
`globalPseudoMassDistRestrictedRate_le_pseudoMassFromParamsAtPairDist`. -/
theorem globalPseudoMassDistRestrictedRate_le_globalPseudoMassDist
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (hβJ_pos : 0 < β * J)
    (hβJd_pos : 0 < β * J * (2 * d))
    (hβJd_half : β * J * (2 * d) < 1 / 2) :
    globalPseudoMassDistRestrictedRate α d J β ≤
      globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold globalPseudoMassDist
  refine le_csInf
    (globalPseudoMassDistSet_nonempty_of_high_temp hα hd hβ hβJ_pos) ?_
  rintro m ⟨x, z, hactive, rfl⟩
  exact globalPseudoMassDistRestrictedRate_le_pseudoMassFromParamsAtPairDist
    hα hJ hβ hβJ_pos hβJd_pos hβJd_half hactive.1

/-- **Restricted high-temperature upper constant** for GJ §17.5 Lemma 17.5.2:
the ratio `C = (−log(tanh(βJ))) / M` of the high-temperature lattice-mass ceiling
to the restricted pair-uniform rate `M = globalPseudoMassDistRestrictedRate`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
noncomputable def globalPseudoMassDistRestrictedUpperConst
    (α d : ℕ) (J β : ℝ) : ℝ :=
  (-Real.log (Real.tanh (β * J))) /
    globalPseudoMassDistRestrictedRate α d J β

/-- **GJ §17.5 Lemma 17.5.2 tractable restricted upper bound** `m(σ) ≤ C·m⁻(σ)`:
on the strict high-temperature window of the cubic exhaustion, the lattice mass
is dominated by the restricted upper constant times the distance-parametrized
system pseudo-mass.

Proof: the lattice mass is `≤ ENNReal.ofReal B` with `B = −log(tanh(βJ))`
(`latticeMass_le_neg_log_tanh_betaJ`); writing `B = C · M` (with
`C = B/M`, `M = globalPseudoMassDistRestrictedRate > 0`) and pushing the product
through `ENNReal.ofReal_mul`, the pair-uniform lower bound `M ≤ globalPseudoMassDist`
upgrades the right factor by `ENNReal` multiplication monotonicity.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem latticeMass_le_globalPseudoMassDist_restrictedUpper
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_half : β * J * (2 * d) < 1 / 2) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistRestrictedUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  -- Derived window facts.
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  have hβJd_pos : 0 < β * J * (2 * d) := mul_pos hβJ_pos (by linarith)
  -- Pair-uniform lower bound and rate positivity.
  have hgpmd :
      globalPseudoMassDistRestrictedRate α d J β ≤
        globalPseudoMassDist hα (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) :=
    globalPseudoMassDistRestrictedRate_le_globalPseudoMassDist
      hα hd hJ.le hβ hβJ_pos hβJd_pos hβJd_half
  have hM_pos : 0 < globalPseudoMassDistRestrictedRate α d J β :=
    globalPseudoMassDistRestrictedRate_pos hβJd_pos hβJd_half
  -- `B := −log(tanh(βJ)) ≥ 0` since `tanh(βJ) ∈ (0,1)`.
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos _)
  have hB_nonneg : 0 ≤ -Real.log (Real.tanh (β * J)) := by
    have hlog := Real.log_neg htanh_pos (Real.tanh_lt_one _)
    linarith
  have hC_nonneg : 0 ≤ globalPseudoMassDistRestrictedUpperConst α d J β := by
    unfold globalPseudoMassDistRestrictedUpperConst
    exact div_nonneg hB_nonneg hM_pos.le
  -- `B = C · M`.
  have hBeq :
      -Real.log (Real.tanh (β * J))
        = globalPseudoMassDistRestrictedUpperConst α d J β
            * globalPseudoMassDistRestrictedRate α d J β := by
    unfold globalPseudoMassDistRestrictedUpperConst
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)]
  calc
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
          latticeMass_le_neg_log_tanh_betaJ hd hJ hβ
    _ = ENNReal.ofReal (globalPseudoMassDistRestrictedUpperConst α d J β
          * globalPseudoMassDistRestrictedRate α d J β) := by rw [hBeq]
    _ = ENNReal.ofReal (globalPseudoMassDistRestrictedUpperConst α d J β)
          * ENNReal.ofReal (globalPseudoMassDistRestrictedRate α d J β) :=
          ENNReal.ofReal_mul hC_nonneg
    _ ≤ ENNReal.ofReal (globalPseudoMassDistRestrictedUpperConst α d J β)
          * ENNReal.ofReal
              (globalPseudoMassDist hα (cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ)) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hgpmd) _

/-- **GJ §17.5 Lemma 17.5.2 faithful restricted sandwich**
`m⁻(σ) ≤ m(σ) ≤ C·m⁻(σ)`: on the strict high-temperature window of the cubic
exhaustion, the lattice mass is sandwiched between the distance-parametrized
system pseudo-mass and the restricted upper constant times that same
pseudo-mass.

This bundles the merged unconditional lower bound
`globalPseudoMassDist_le_latticeMass` with the tractable restricted upper bound
`latticeMass_le_globalPseudoMassDist_restrictedUpper`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem globalPseudoMassDist_restrictedSandwich
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_half : β * J * (2 * d) < 1 / 2) :
    ENNReal.ofReal
        (globalPseudoMassDist hα (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ)) ≤
      latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistRestrictedUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨globalPseudoMassDist_le_latticeMass hα (cubicExhaustion d) hJ.le hβ,
   latticeMass_le_globalPseudoMassDist_restrictedUpper hα hd hJ hβ hβJd_half⟩

end Ambient
end IsingModel
