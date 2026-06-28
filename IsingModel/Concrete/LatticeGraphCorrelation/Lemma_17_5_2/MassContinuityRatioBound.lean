import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UnconditionalFiniteRegionLipschitz

/-!
# GJ §17.5 Theorem 17.5.1 — analytic heart (PR-1): the m⁻-rate correlation majorant

This module begins the formalization of the genuine Glimm--Jaffe proof of Theorem 17.5.1 (the mass
`m(σ)` is continuous), following GJ 2nd ed. §17.5 pp.~311--312.  The crux is the GJ majorization of
the two-point function by the *system* pseudo-mass profile, which (combined with the sharp HLS
convolution and the triangle exp-cancellation, #4325--#4329) gives a derivative-ratio bound scaling
linearly in the lattice distance, hence a Lipschitz constant uniform in the region `A`.

This file provides the first ingredient: every two-point function is dominated by the profile at the
**system** rate `globalPseudoMassDist` (the infimum over all distinct pairs), because each
correlation equals the profile at its own per-pair mass (`pseudoMass` identity) and the system mass
is no larger
(`globalPseudoMassDist_le_of_active`), while `pseudoMassG` is antitone in the rate.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set

/-- **GJ §17.5 per-pair pseudo-mass defining identity (cubic exhaustion).**  For a distinct pair
`x ≠ y` with active correlation, the two-point function equals the distance profile at its own
per-pair pseudo-mass: `⟨φ_x φ_y⟩ = pseudoMassG α (dist x y) (m⁻(x,y))`.  This is GJ's (17.5.3) — the
denominator of the p.312 ratio is handled by this identity (not majorized).  Proof:
`pseudoMassFromParamsAtPairDist = pseudoMassExt = pseudoMass` on the active range, and
`pseudoMass_spec`. -/
theorem correlationInfinite_eq_pseudoMassG_pairDist
    {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y}
      = pseudoMassG α (IsingModel.latticeDistance d x y : ℝ)
          (pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) x y) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x y : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxy ((IsingModel.latticeDistance_eq_zero_iff d x y).mp h))
  have hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, y} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x y hxy
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (Ambient.cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) hxy hpos, pseudoMassExt_of_mem hα hpos hcorr,
    pseudoMass_spec hα hpos hcorr]

/-- **GJ §17.5 system-mass correlation majorant.**  For a distinct pair `x ≠ w` with active
correlation, the two-point function is dominated by the distance profile at the *system* pseudo-mass
`m⁻(σ) = globalPseudoMassDist`:
`⟨φ_x φ_w⟩ ≤ pseudoMassG α (dist x w) (globalPseudoMassDist)`.

Proof (GJ p.312 "m⁻ majorizes each factor of the numerator"): the correlation equals the profile at
its own per-pair mass `m⁻(x,w)` (the `pseudoMass` defining identity for the active pair); the system
mass `m⁻(σ) ≤ m⁻(x,w)` (`globalPseudoMassDist_le_of_active`); and `pseudoMassG α r ·` is antitone on
`Ici 0`, so lowering the rate raises the profile. -/
theorem correlationInfinite_le_pseudoMassG_globalPseudoMassDist
    {α d : ℕ} (hα : 1 ≤ α)
    {J β : ℝ} (hJ_pos : 0 < J) (hβ : 0 < β)
    {x w : Fin d → ℤ} (hxw : x ≠ w) :
    Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, w}
      ≤ pseudoMassG α (IsingModel.latticeDistance d x w : ℝ)
          (globalPseudoMassDist hα (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x w : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxw ((IsingModel.latticeDistance_eq_zero_iff d x w).mp h))
  have hcorr : Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, w} ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos_exhaustion
      (Ambient.cubicExhaustion d) hβ (mul_pos hβ hJ_pos) x w hxw
  set m_xw : ℝ := pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) x w with hm_xw_def
  set m_sys : ℝ := globalPseudoMassDist hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) with hm_sys_def
  -- correlation = profile at its own per-pair mass (identity).
  have hid : pseudoMassG α (IsingModel.latticeDistance d x w : ℝ) m_xw
      = Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, w} := by
    rw [hm_xw_def, pseudoMassFromParamsAtPairDist_of_ne hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hxw hpos, pseudoMassExt_of_mem hα hpos hcorr]
    exact pseudoMass_spec hα hpos hcorr
  -- system mass ≤ per-pair mass.
  have hle : m_sys ≤ m_xw := by
    rw [hm_sys_def, hm_xw_def]
    exact globalPseudoMassDist_le_of_active hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) ⟨hxw, hcorr⟩
  have hm_sys_nn : 0 ≤ m_sys := by
    rw [hm_sys_def]; exact globalPseudoMassDist_nonneg hα (Ambient.cubicExhaustion d) _
  have hm_xw_nn : 0 ≤ m_xw := by
    rw [hm_xw_def]; exact pseudoMassFromParamsAtPairDist_nonneg hα (Ambient.cubicExhaustion d) _ x w
  -- antitone in the rate: lowering m raises the profile.
  rw [← hid]
  exact pseudoMassG_antitoneOn hα hpos (Set.mem_Ici.mpr hm_sys_nn)
    (Set.mem_Ici.mpr hm_xw_nn) hle

end Ambient
end IsingModel
