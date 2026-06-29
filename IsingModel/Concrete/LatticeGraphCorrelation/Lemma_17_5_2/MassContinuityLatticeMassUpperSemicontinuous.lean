import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityLatticeMassDirectionalLowerBound
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityCorrelationLengthUpperSemicontinuous

/-!
# GJ Theorem 17.5.1 — upper-semicontinuity of the true mass on the window (usc half of continuity)

Combining the mass characterization
`latticeMass = ⨅_{v≠0} ofReal(directionalInverseCorrelationLength v)`
(`latticeMass_eq_iInf_ofReal_directionalInverseCorrelationLength`) with the
upper-semicontinuity of each directional inverse correlation length
(`directionalInverseCorrelationLength_upperSemicontinuousOn_window`), the **true mass
`latticeMass`** is **upper-semicontinuous in `β`** on the high-temperature window
`Ioo 0 (1/(J·2d))`:

`UpperSemicontinuousOn (β ↦ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩) (Ioo 0 (1/(J·2d)))`.

This is the **upper-semicontinuous half** of GJ Theorem 17.5.1 (continuity of the true mass, #4386).
On the window `latticeMass` equals an infimum (over directions) of `ENNReal.ofReal`-images of the
upper-semicontinuous per-direction lengths, and an infimum of upper-semicontinuous functions is
upper-semicontinuous (`upperSemicontinuousOn_iInf`); the equality with `latticeMass` transfers it
via `UpperSemicontinuousWithinAt.congr_of_eventuallyEq`.

The **lower-semicontinuous** half (and hence full continuity) is the genuinely open Ornstein–Zernike
content (#4386) — it would need continuity, not just upper-semicontinuity, of the directional rates.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, pp.~311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel
namespace Ambient

open Set

variable {d : ℕ}

/-- **Upper-semicontinuity of the true mass `latticeMass` on the high-temperature window** (usc half
of GJ Theorem 17.5.1, #4386).  For `d ≥ 1` and `0 < J`, the map
`β ↦ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩` is `UpperSemicontinuousOn` the window
`Ioo 0 (1/(J·2d))`.  By `latticeMass_eq_iInf_ofReal_directionalInverseCorrelationLength` (with the
`directionalInverseCorrelationLength_eq_iInf_div` form of each directional length) `latticeMass`
agrees on the window with the infimum over directions of the `ENNReal.ofReal`-images of the
upper-semicontinuous per-direction functions; that infimum is upper-semicontinuous
(`upperSemicontinuousOn_iInf` + `ENNReal.continuous_ofReal.comp_upperSemicontinuousOn`), and the
equality transfers via `UpperSemicontinuousWithinAt.congr_of_eventuallyEq`. -/
theorem latticeMass_upperSemicontinuousOn_window {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d) :
    UpperSemicontinuousOn
      (fun β => latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  -- the clean `⨅`-of-`ofReal` envelope (no proof-dependent arguments) is upper-semicontinuous.
  have hH : UpperSemicontinuousOn
      (fun β => ⨅ v : {v : Fin d → ℤ // v ≠ 0}, ENNReal.ofReal ((⨅ n : ↥(Set.Ici (1 : ℕ)),
        directionalLogCorr J β v.1 (n : ℕ) / ((n : ℕ) : ℝ)) / (latticeDistance d 0 v.1 : ℝ)))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
    apply upperSemicontinuousOn_iInf
    intro v
    exact ENNReal.continuous_ofReal.comp_upperSemicontinuousOn
      (directionalInverseCorrelationLength_upperSemicontinuousOn_window hd hJ v.2)
      ENNReal.ofReal_mono
  intro β hβ
  refine (hH β hβ).congr_of_eventuallyEq hβ (eventually_nhdsWithin_of_forall ?_)
  intro x hx
  -- on the window the envelope equals `latticeMass`.
  have hcongr : (⨅ v : {v : Fin d → ℤ // v ≠ 0}, ENNReal.ofReal ((⨅ n : ↥(Set.Ici (1 : ℕ)),
        directionalLogCorr J x v.1 (n : ℕ) / ((n : ℕ) : ℝ)) / (latticeDistance d 0 v.1 : ℝ)))
      = ⨅ v : {v : Fin d → ℤ // v ≠ 0},
          ENNReal.ofReal (directionalInverseCorrelationLength hJ hx.1 v.2) := by
    refine iInf_congr fun v => ?_
    rw [directionalInverseCorrelationLength_eq_iInf_div hJ hx.1 v.2]
  have heq := hcongr.trans
    (latticeMass_eq_iInf_ofReal_directionalInverseCorrelationLength hJ hx.1 hd).symm
  intro y
  simp only [heq]

end Ambient
end IsingModel
