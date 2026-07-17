import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityUniformInfLipschitz
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCorrelationLengthUpperSemicontinuous
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityLatticeMassDirectionalLowerBound

/-!
# GJ Theorem 17.5.1 — true-mass continuity, gated on the uniform-in-direction Lipschitz bound

The upper-semicontinuous half of GJ Theorem 17.5.1 is unconditional
(`latticeMass_upperSemicontinuousOn_window`).  The **lower-semicontinuous** half — equivalently full
**continuity** — is the genuine Ornstein–Zernike content (#4386): it reduces, via the mass identity
`latticeMass = ofReal(⨅_{v≠0} directionalInverseCorrelationLength v)`, to the **continuity** of the
real envelope `β ↦ ⨅_{v≠0} directionalInverseCorrelationLength(v)`.  An infimum of continuous
functions is continuous once the family is *uniformly* Lipschitz on each compact subinterval.  (For
context only — not used by the proof below — the per-direction rates are individually continuous,
cf. `perPairRate_continuousOn_window`; what is missing and supplied here as the hypothesis `hLip` is
the **uniform-in-`v` Lipschitz/derivative bound**, the un-formalized OZ estimate = the
differentiated cluster expansion of `log⟨φ₀φ_x⟩`, GJ p.312.)

This file isolates that single ingredient as an explicit **hypothesis** `hLip` and proves that it
yields the full continuity theorem.  Supplying `hLip` (a dedicated multi-session OZ sub-project)
immediately discharges GJ Theorem 17.5.1.  The result is axiom-free; `hLip` is a hypothesis, not an
axiom.  The abstract closer `abs_csInf_envelope_sub_le_of_uniform_lipschitz` (an infimum of a
uniformly-Lipschitz family is Lipschitz, with **no** binding/attainment hypothesis) does the work,
avoiding the non-attainment obstruction `m_{x,z} ↓ m∞` of the pseudo-mass route.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, p.~312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel
namespace Ambient

open Set Filter Topology

variable {d : ℕ}

/-- **Proof-free directional rate function** `β ↦ (⨅_{n≥1} −log⟨φ₀φ_{nv}⟩/n) / d(0,v)` — the
`directionalInverseCorrelationLength` of direction `v` written without the `0<β` proof argument, so
it can be treated as an honest function of `β` (it agrees with
`directionalInverseCorrelationLength` for `0<β` via the `_eq_iInf_div` rewrite). -/
noncomputable def directionalRateFn (J : ℝ) (d : ℕ) (v : Fin d → ℤ) (β : ℝ) : ℝ :=
  (⨅ n : ↥(Set.Ici (1 : ℕ)), directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
    / (latticeDistance d 0 v : ℝ)

/-- `directionalRateFn` agrees with `directionalInverseCorrelationLength` for `0 < β`. -/
theorem directionalRateFn_eq {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ} (hv : v ≠ 0) :
    directionalRateFn J d v β = directionalInverseCorrelationLength hJ hβ hv :=
  (directionalInverseCorrelationLength_eq_iInf_div hJ hβ hv).symm

/-- Nonnegativity of `directionalRateFn` for `0 < β`. -/
theorem directionalRateFn_nonneg {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) {v : Fin d → ℤ} (hv : v ≠ 0) :
    0 ≤ directionalRateFn J d v β := by
  rw [directionalRateFn_eq hJ hβ hv]
  exact directionalInverseCorrelationLength_nonneg hJ hβ hv

/-- Boundedness below (by `0`) of the directional-rate range at a positive `β`. -/
theorem directionalRateFn_range_bddBelow {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) (d : ℕ) :
    BddBelow (Set.range fun v : {v : Fin d → ℤ // v ≠ 0} => directionalRateFn J d v.1 β) := by
  refine ⟨0, ?_⟩
  rintro x ⟨v, rfl⟩
  exact directionalRateFn_nonneg hJ hβ v.2

/-- **GJ Theorem 17.5.1 (continuity of the true mass), gated on the uniform-in-direction Lipschitz
bound.**  Given the hypothesis `hLip` — on each compact subinterval `[β₁,β₂]` of the window there is
a single Lipschitz constant `L` valid for **every** direction `v` — the true mass
`β ↦ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩` is `ContinuousOn` the window `Ioo 0 (1/(J·2d))`.

`hLip` is the genuine Ornstein–Zernike ingredient (the differentiated cluster expansion / uniform
rate-derivative bound, GJ p.312) and is left as a hypothesis for a dedicated sub-project; everything
else here is unconditional and axiom-free.  The proof: on the window `latticeMass` equals
`ofReal(⨅_v directionalRateFn v)`; `hLip` + `abs_csInf_envelope_sub_le_of_uniform_lipschitz` make
the real envelope Lipschitz, hence continuous, on each compact subinterval, hence continuous at
every interior point; `ENNReal.ofReal` is continuous; the equality transfers it to `latticeMass`. -/
theorem latticeMass_continuousOn_window_of_uniform_lipschitz {J : ℝ} (hJ : 0 < J) {d : ℕ}
    (hd : 1 ≤ d)
    (hLip : ∀ β₁ β₂ : ℝ, 0 < β₁ → β₁ ≤ β₂ → β₂ < 1 / (J * ↑(2 * d)) →
      ∃ L : ℝ, ∀ v : {v : Fin d → ℤ // v ≠ 0}, ∀ β ∈ Set.Icc β₁ β₂, ∀ β' ∈ Set.Icc β₁ β₂,
        |directionalRateFn J d v.1 β' - directionalRateFn J d v.1 β| ≤ L * |β' - β|) :
    ContinuousOn (fun β => latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  haveI : NeZero d := ⟨Nat.one_le_iff_ne_zero.mp hd⟩
  set B : ℝ := 1 / (J * ↑(2 * d)) with hB
  -- the real envelope `β ↦ ⨅_v directionalRateFn v` is continuous on the window.
  have hcont_env : ContinuousOn
      (fun β => ⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 β) (Set.Ioo 0 B) := by
    intro x hx
    -- compact subinterval `[β₁,β₂]` around `x`.
    obtain ⟨hx0, hxB⟩ := hx
    set β₁ : ℝ := x / 2 with hβ₁
    set β₂ : ℝ := (x + B) / 2 with hβ₂
    have hβ₁0 : 0 < β₁ := by rw [hβ₁]; linarith
    have hβ₁x : β₁ < x := by rw [hβ₁]; linarith
    have hxβ₂ : x < β₂ := by rw [hβ₂]; linarith
    have hβ₂B : β₂ < B := by rw [hβ₂]; linarith
    have hβ₁₂ : β₁ ≤ β₂ := le_of_lt (lt_trans hβ₁x hxβ₂)
    obtain ⟨L, hL⟩ := hLip β₁ β₂ hβ₁0 hβ₁₂ hβ₂B
    -- the envelope is `L⁺`-Lipschitz on `Icc β₁ β₂`.
    have hlip : LipschitzOnWith L.toNNReal
        (fun β => ⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 β)
        (Set.Icc β₁ β₂) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha b hb
      have ha0 : 0 < a := lt_of_lt_of_le hβ₁0 ha.1
      have hb0 : 0 < b := lt_of_lt_of_le hβ₁0 hb.1
      -- reduce to `|env a − env b| ≤ L|a−b|`.
      have hcore : |(⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 a)
          - ⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 b| ≤ L * |a - b| := by
        rcases le_total b a with hba | hab
        · have hbl : ∀ v : {v : Fin d → ℤ // v ≠ 0},
              |directionalRateFn J d v.1 a - directionalRateFn J d v.1 b| ≤ L * (a - b) := by
            intro v
            have h := hL v b hb a ha
            rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)] at h
          have hkey := abs_csInf_envelope_sub_le_of_uniform_lipschitz
            (g := fun v : {v : Fin d → ℤ // v ≠ 0} => fun β => directionalRateFn J d v.1 β)
            (directionalRateFn_range_bddBelow hJ hb0 d)
            (directionalRateFn_range_bddBelow hJ ha0 d) hbl
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
          exact hkey
        · have hbl : ∀ v : {v : Fin d → ℤ // v ≠ 0},
              |directionalRateFn J d v.1 b - directionalRateFn J d v.1 a| ≤ L * (b - a) := by
            intro v
            have h := hL v a ha b hb
            rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at h
          have hkey := abs_csInf_envelope_sub_le_of_uniform_lipschitz
            (g := fun v : {v : Fin d → ℤ // v ≠ 0} => fun β => directionalRateFn J d v.1 β)
            (directionalRateFn_range_bddBelow hJ ha0 d)
            (directionalRateFn_range_bddBelow hJ hb0 d) hbl
          have hab_abs : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          rw [hab_abs, abs_sub_comm]
          exact hkey
      rw [Real.dist_eq, Real.dist_eq]
      refine hcore.trans ?_
      gcongr
      rw [Real.coe_toNNReal']
      exact le_max_left _ _
    -- continuity at `x` from Lipschitz on a neighbourhood.
    have hIcc_nhds : Set.Icc β₁ β₂ ∈ 𝓝 x := Icc_mem_nhds hβ₁x hxβ₂
    exact (hlip.continuousOn.continuousAt hIcc_nhds).continuousWithinAt
  -- transfer to `latticeMass` via the mass identity (on the window) and `ofReal` continuity.
  have hofR : ContinuousOn
      (fun β => ENNReal.ofReal (⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 β))
      (Set.Ioo 0 B) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont_env
  refine hofR.congr ?_
  intro x hx
  -- on the window `latticeMass = ofReal(envelope)`.
  change latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, x⟩ : IsingParams ℝ)
    = ENNReal.ofReal (⨅ v : {v : Fin d → ℤ // v ≠ 0}, directionalRateFn J d v.1 x)
  rw [latticeMass_eq_iInf_ofReal_directionalInverseCorrelationLength hJ hx.1 hd,
    ENNReal.ofReal_iInf]
  refine iInf_congr fun v => ?_
  rw [directionalRateFn_eq hJ hx.1 v.2]

end Ambient
end IsingModel
