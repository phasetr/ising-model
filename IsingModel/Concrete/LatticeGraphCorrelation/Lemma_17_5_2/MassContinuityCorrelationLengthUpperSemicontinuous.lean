import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityOnAxisCorrelationLength
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityDirectionalCorrelationLength
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityPerPairRate
import Mathlib.Topology.Semicontinuity.Basic

/-!
# GJ §17.5 / FV §3.7.3 — upper-semicontinuity of the inverse correlation length on the window

A **correlation-length regularity** result: the (well-defined) inverse correlation length is
**upper-semicontinuous in `β`** on the high-temperature window `Ioo 0 (1/(J·2d))`, in both the
on-axis form `onAxisInverseCorrelationLength` and the directional form
`directionalInverseCorrelationLength v` (`v ≠ 0`).

Each length is the Fekete limit `Subadditive.lim = sInf ((n ↦ a(n)/n) '' Ici 1)` of the subadditive
log-correlation `a(n) = −log⟨φ₀ φ_{n·v}⟩_∞`.  Each normalised term `β ↦ a(n)/n` (`n ≥ 1`) is
`ContinuousOn` the window — the infinite-volume correlation is continuous and strictly positive at
high temperature (`correlationInfinite_continuousAt_beta_of_high_temp`,
`correlationInfinite_pos_of_betaJ_pos_pair`), so `−log` of it is continuous, and dividing by the
fixed index `n` keeps continuity — hence upper-semicontinuous.  The infimum over `n ≥ 1` of an
upper-semicontinuous family is upper-semicontinuous (`upperSemicontinuousOn_ciInf`, bounded below by
`0`).  For the directional length the further division by the fixed positive distance `d(0,v)` is a
continuous monotone post-composition (`Continuous.comp_upperSemicontinuousOn`).

## Scope (honest)

This is a **side regularity result**, *not* GJ Theorem 17.5.1.  The true mass
`latticeMass = sSup {α : HasExponentialDecay α}` is the abscissa of *uniform* exponential decay; for
`d ≥ 2` the directional / on-axis inverse correlation length is a strict **upper bound** on
`latticeMass` (the diagonal direction decays slower), so upper-semicontinuity of the length does
**not** yield upper-semicontinuity (let alone continuity) of the true mass.  The matching lower
bound — the Ornstein–Zernike exact rate — remains the open research wall (#4386).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 eq. (17.5.1) / Theorem 17.5.1, pp.~311--312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3 (correlation length).
-/

namespace IsingModel
namespace Ambient

open Set

variable {d : ℕ}

/-- **On-axis inverse correlation length as an indexed infimum over `n ≥ 1`**: the Fekete limit
`Subadditive.lim` unfolds to `sInf ((n ↦ u(n)/n) '' Ici 1)`, which is the indexed infimum
`⨅ n : ↥(Ici 1), u(n)/n` (range of the subtype coercion is `Ici 1`).  This rewrites the named
length into the `⨅`-form on which `upperSemicontinuousOn_ciInf` applies. -/
theorem onAxisInverseCorrelationLength_eq_iInf (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    onAxisInverseCorrelationLength hd hJ hβ
      = ⨅ n : ↥(Set.Ici (1 : ℕ)), onAxisLogCorr hd J β (n : ℕ) / ((n : ℕ) : ℝ) := by
  simp only [onAxisInverseCorrelationLength, Subadditive.lim]
  rw [show (⨅ n : ↥(Set.Ici (1 : ℕ)), onAxisLogCorr hd J β (n : ℕ) / ((n : ℕ) : ℝ))
        = sInf (Set.range fun n : ↥(Set.Ici (1 : ℕ)) =>
            onAxisLogCorr hd J β (n : ℕ) / ((n : ℕ) : ℝ)) from rfl]
  congr 1
  rw [show (fun n : ↥(Set.Ici (1 : ℕ)) => onAxisLogCorr hd J β (n : ℕ) / ((n : ℕ) : ℝ))
        = (fun m : ℕ => onAxisLogCorr hd J β m / (m : ℝ)) ∘ (Subtype.val) from rfl,
    Set.range_comp, Subtype.range_coe]

/-- **On-axis normalised log-correlation term is continuous on the window**: for `n ≥ 1`, the map
`β ↦ u(n)/n = −log⟨φ₀ φ_{n e₁}⟩_∞ / n` is `ContinuousOn` the high-temperature window.  The pair
`{0, n e₁}` is distinct (`n ≥ 1`), so the correlation is continuous and strictly positive, `−log` is
continuous, and `÷ n` preserves continuity. -/
theorem onAxisLogCorr_div_continuousOn_window (hd : 0 < d) {J : ℝ} (hJ : 0 < J) {n : ℕ}
    (hn : 1 ≤ n) :
    ContinuousOn (fun β => onAxisLogCorr hd J β n / (n : ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have hne : (0 : Fin d → ℤ) ≠ onAxisPoint hd n := by
    rw [← onAxisPoint_zero hd]
    exact onAxisPoint_ne hd (by omega)
  intro β₀ hβ₀
  refine ContinuousAt.continuousWithinAt ?_
  have hcorr_cont : ContinuousAt (fun β => Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd n}) β₀ :=
    correlationInfinite_continuousAt_beta_of_high_temp hd (cubicExhaustion d) _ _ hne J hJ β₀ hβ₀
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₀⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), onAxisPoint hd n} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ₀.1 (mul_pos hβ₀.1 hJ) hne
  exact ((hcorr_cont.log (ne_of_gt hcorr_pos)).neg).div_const _

/-- **Upper-semicontinuity of the on-axis inverse correlation length on the window** (GJ §17.5 /
FV §3.7.3 correlation-length regularity; toward but NOT closing Thm 17.5.1 / #4386).  On the
high-temperature window, `β ↦ onAxisInverseCorrelationLength` (`= ⨅ n : ↥(Ici 1), u(n)/n`, by
`onAxisInverseCorrelationLength_eq_iInf`) is upper-semicontinuous: an infimum over `n ≥ 1` of the
continuous (hence upper-semicontinuous) normalised terms, bounded below by `0`.  This is *not*
upper-semicontinuity of the true mass `latticeMass` — for `d ≥ 2` the on-axis rate strictly exceeds
the mass. -/
theorem onAxisInverseCorrelationLength_upperSemicontinuousOn_window (hd : 0 < d) {J : ℝ}
    (hJ : 0 < J) :
    UpperSemicontinuousOn
      (fun β => ⨅ n : ↥(Set.Ici (1 : ℕ)), onAxisLogCorr hd J β (n : ℕ) / ((n : ℕ) : ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  apply upperSemicontinuousOn_ciInf
  · intro β hβ
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (onAxisLogCorr_nonneg hd hJ hβ.1 _) (Nat.cast_nonneg _)
  · intro n
    exact (onAxisLogCorr_div_continuousOn_window hd hJ n.2).upperSemicontinuousOn

/-- **Directional inverse correlation length as an indexed infimum over `n ≥ 1`, divided by
`d(0,v)`**: the directional Fekete limit `Subadditive.lim` unfolds to
`sInf ((n ↦ a_v(n)/n) '' Ici 1) = ⨅ n : ↥(Ici 1), a_v(n)/n`, and the directional length is this
divided by the per-step distance `d(0,v)`. -/
theorem directionalInverseCorrelationLength_eq_iInf_div {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {v : Fin d → ℤ} (hv : v ≠ 0) :
    directionalInverseCorrelationLength hJ hβ hv
      = (⨅ n : ↥(Set.Ici (1 : ℕ)), directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
        / (latticeDistance d 0 v : ℝ) := by
  rw [directionalInverseCorrelationLength]
  congr 1
  simp only [Subadditive.lim]
  rw [show (⨅ n : ↥(Set.Ici (1 : ℕ)), directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
        = sInf (Set.range fun n : ↥(Set.Ici (1 : ℕ)) =>
            directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ)) from rfl]
  congr 1
  rw [show (fun n : ↥(Set.Ici (1 : ℕ)) => directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
        = (fun m : ℕ => directionalLogCorr J β v m / (m : ℝ)) ∘ (Subtype.val) from rfl,
    Set.range_comp, Subtype.range_coe]

/-- **Directional normalised log-correlation term is continuous on the window**: for `v ≠ 0` and
`n ≥ 1`, the map `β ↦ a_v(n)/n = −log⟨φ₀ φ_{n·v}⟩_∞ / n` is `ContinuousOn` the high-temperature
window.  The ray point `n·v` is nonzero, so the same correlation continuity + positivity argument as
the on-axis case applies. -/
theorem directionalLogCorr_div_continuousOn_window (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J)
    {v : Fin d → ℤ} (hv : v ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn (fun β => directionalLogCorr J β v n / (n : ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have hne : (0 : Fin d → ℤ) ≠ n • v := nsmul_ne_zero_of_dir hv (by omega)
  intro β₀ hβ₀
  refine ContinuousAt.continuousWithinAt ?_
  have hcorr_cont : ContinuousAt (fun β => Ambient.correlationInfinite (IsingModel.latticeGraph d)
      (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v}) β₀ :=
    correlationInfinite_continuousAt_beta_of_high_temp hd (cubicExhaustion d) _ _ hne J hJ β₀ hβ₀
  have hcorr_pos : 0 < Ambient.correlationInfinite (IsingModel.latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β₀⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), n • v} :=
    correlationInfinite_pos_of_betaJ_pos_pair hβ₀.1 (mul_pos hβ₀.1 hJ) hne
  exact ((hcorr_cont.log (ne_of_gt hcorr_pos)).neg).div_const _

/-- **Upper-semicontinuity of the directional inverse correlation length on the window** (GJ §17.5 /
FV §3.7.3 correlation-length regularity; toward but NOT closing Thm 17.5.1 / #4386).  For `v ≠ 0`,
`β ↦ directionalInverseCorrelationLength v` (`= (⨅ n : ↥(Ici 1), a_v(n)/n) / d(0,v)`, by
`directionalInverseCorrelationLength_eq_iInf_div`) is upper-semicontinuous on the high-temperature
window: the inner infimum over `n ≥ 1` of the continuous normalised terms is upper-semicontinuous
(`upperSemicontinuousOn_ciInf`, bounded below by `0`), and the division by the fixed positive
distance `d(0,v)` is a continuous monotone post-composition.  This is *not* upper-semicontinuity of
the true mass `latticeMass`. -/
theorem directionalInverseCorrelationLength_upperSemicontinuousOn_window (hd : 1 ≤ d) {J : ℝ}
    (hJ : 0 < J) {v : Fin d → ℤ} (hv : v ≠ 0) :
    UpperSemicontinuousOn
      (fun β => (⨅ n : ↥(Set.Ici (1 : ℕ)), directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
        / (latticeDistance d 0 v : ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  have hD0 : (0 : ℝ) < (latticeDistance d 0 v : ℝ) := by
    have hne : latticeDistance d 0 v ≠ 0 := fun h =>
      hv (((latticeDistance_eq_zero_iff d 0 v).mp h).symm)
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hinf : UpperSemicontinuousOn
      (fun β => ⨅ n : ↥(Set.Ici (1 : ℕ)), directionalLogCorr J β v (n : ℕ) / ((n : ℕ) : ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
    apply upperSemicontinuousOn_ciInf
    · intro β hβ
      refine ⟨0, ?_⟩
      rintro x ⟨n, rfl⟩
      exact div_nonneg (directionalLogCorr_nonneg hJ hβ.1 v _) (Nat.cast_nonneg _)
    · intro n
      exact (directionalLogCorr_div_continuousOn_window hd hJ hv n.2).upperSemicontinuousOn
  exact (continuous_id.div_const (latticeDistance d 0 v : ℝ)).comp_upperSemicontinuousOn hinf
    (fun a b hab => by simp only [id_eq]; gcongr)

end Ambient
end IsingModel
