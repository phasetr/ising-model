import IsingModel.ClusterExpansion.MayerCore.TermsComplexHolomorphic
import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Volume-uniform per-site Kotecky--Preiss Mayer--Montroll identity (GJ §18.6)

This is PR-C of issue #4149 (§18.6), the capstone of the per-site Kotecky--Preiss Mayer
identity.  The existing identity `mayer_identity_general_t` holds on a neighbourhood of `0`
whose size depends on the volume (through the *full* partition-function convergence radius);
here we upgrade it to the *volume-uniform* radius `T` determined only by the maximal degree
`Δ = G.maxDegree`, via analytic continuation (the identity theorem).

The mechanism:

* The complexified Mayer series `F : z ↦ ∑' n, mayerExpansionTermComplex G n z` is holomorphic
  on `ball 0 T` (PR-B, `mayerExpansionTermComplex_tsum_differentiableOn_ball`), hence
  `AnalyticOnNhd ℂ` (`DifferentiableOn.analyticOnNhd`) and so `AnalyticOnNhd ℝ` after
  `restrictScalars`.
* The real Mayer series `g : t ↦ ∑' n, mayerExpansionTerm G n t` agrees on the reals with
  `Complex.re ∘ F ∘ Complex.ofReal` (`mayerExpansionTermComplex_ofReal`, `Complex.ofReal_tsum`),
  so `g` is real-analytic on `Ioo (-T) T` as a composition of analytic maps.
* The polymer free energy `s ↦ polymerFreeEnergy G s` is real-analytic on `Ici 0`
  (`polymerFreeEnergy_analyticOnNhd_Ici_zero`) and agrees with `g` on a neighbourhood of `0`
  (`mayer_identity_general_t_eventually`).
* Both functions are analytic on the preconnected set `Ico 0 T` containing `0`, so the identity
  theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) extends the agreement to all of
  `Ico 0 T`.

Since `T` depends only on `Δ`, the resulting identity is volume-uniform — the key advantage over
`mayer_identity_general_t`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.5--§18.6, pp.~335--340.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Real-analyticity of the Mayer tsum on a Kotecky--Preiss interval** (GJ §18.6).  Under the
volume-uniform per-site Kotecky--Preiss conditions at radius `T` (`Δ²eT < 1` and
`4·Δ²eT/(1−Δ²eT)² < 1`), the real Mayer series `t ↦ ∑' n, mayerExpansionTerm G n t` is
`AnalyticOnNhd ℝ` on the symmetric interval `Ioo (-T) T`.

Proof: the complex Mayer series `F` is holomorphic on `ball 0 T` (PR-B), hence
`AnalyticOnNhd ℂ` (`DifferentiableOn.analyticOnNhd`).  The image `Complex.ofReal '' Ioo (-T) T`
lies in `ball 0 T` (since `‖(↑t : ℂ)‖ = |t| < T`), so `F` is analytic there; the mathlib lemma
`AnalyticOnNhd.re_ofReal` then turns `AnalyticOnNhd ℂ F (ofReal '' Ioo (-T) T)` into
`AnalyticOnNhd ℝ (fun t => (F ↑t).re) (Ioo (-T) T)`.  Finally `(F ↑t).re` equals the real Mayer
series, because `↑(∑' n, mayerExpansionTerm G n t) = ∑' n, mayerExpansionTermComplex G n ↑t = F ↑t`
(`Complex.ofReal_tsum`, `mayerExpansionTermComplex_ofReal`) and `Complex.ofReal_re`. -/
theorem polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ioo (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {T : ℝ} (hT : 0 < T)
    (hkpT : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρT : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun t : ℝ => ∑' n : ℕ, mayerExpansionTerm G n t) (Set.Ioo (-T) T) := by
  -- `F`: the complex Mayer series.
  set F : ℂ → ℂ := fun z => ∑' n : ℕ, mayerExpansionTermComplex G n z with hF
  -- STEP 1: `F` is complex-analytic on `ball 0 T`.
  have hFdiff : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) T) :=
    mayerExpansionTermComplex_tsum_differentiableOn_ball G hT.le hkpT hρT
  have hFan : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) T) :=
    hFdiff.analyticOnNhd Metric.isOpen_ball
  -- STEP 2: `Complex.ofReal '' Ioo (-T) T ⊆ ball 0 T`, so `F` is analytic on that image.
  have hsubset : (Complex.ofReal '' Set.Ioo (-T) T) ⊆ Metric.ball (0 : ℂ) T := by
    rintro w ⟨t, ht, rfl⟩
    rw [Set.mem_Ioo] at ht
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨ht.1, ht.2⟩
  have hFanImg : AnalyticOnNhd ℂ F (Complex.ofReal '' Set.Ioo (-T) T) := hFan.mono hsubset
  -- STEP 3: take real parts via the mathlib `re_ofReal` lemma.
  have hreAn : AnalyticOnNhd ℝ (fun t : ℝ => (F (↑t)).re) (Set.Ioo (-T) T) :=
    hFanImg.re_ofReal
  -- STEP 4: identify `(F ↑t).re` with the real Mayer series.
  have hgeq : (fun t : ℝ => ∑' n : ℕ, mayerExpansionTerm G n t)
      = fun t : ℝ => (F (↑t)).re := by
    funext t
    have hofReal : (↑(∑' n : ℕ, mayerExpansionTerm G n t) : ℂ) = F (↑t) := by
      rw [hF, Complex.ofReal_tsum]
      exact tsum_congr fun n => (mayerExpansionTermComplex_ofReal G n t).symm
    rw [← Complex.ofReal_re (∑' n : ℕ, mayerExpansionTerm G n t), hofReal]
  rw [hgeq]
  exact hreAn

/-- **Real-analyticity of the Mayer tsum on `Ico 0 T`** (GJ §18.6).  The restriction of
`polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ioo` to the half-open interval `Ico 0 T`
(`Set.Ico 0 T ⊆ Set.Ioo (-T) T`), the interval used in the identity-theorem step. -/
theorem polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ico (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {T : ℝ} (hT : 0 < T)
    (hkpT : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρT : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun t : ℝ => ∑' n : ℕ, mayerExpansionTerm G n t) (Set.Ico 0 T) := by
  refine (polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ioo G hT hkpT hρT).mono ?_
  intro t ht
  rw [Set.mem_Ico] at ht
  exact Set.mem_Ioo.mpr ⟨by linarith [ht.1], ht.2⟩

/-- **Volume-uniform per-site Kotecky--Preiss Mayer--Montroll identity** (GJ §18.6).  Under the
per-site Kotecky--Preiss conditions at the volume-uniform radius `T` (`Δ²eT < 1` and
`4·Δ²eT/(1−Δ²eT)² < 1`, where `Δ = G.maxDegree`), the polymer free energy equals the Mayer
expansion for every `t ∈ Ico 0 T`:
`polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t`.

Since `T` depends only on `Δ`, this identity holds on a fixed, volume-independent interval — the
key improvement over the volume-dependent `mayer_identity_general_t`.

Proof (identity theorem): both `s ↦ polymerFreeEnergy G s`
(`polymerFreeEnergy_analyticOnNhd_Ici_zero`, restricted to `Ico 0 T`) and `t ↦ ∑' n,
mayerExpansionTerm G n t` (`polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ico`) are real-analytic on
the preconnected interval `Ico 0 T` (`isPreconnected_Ico`), and they agree on a neighbourhood of
`0 ∈ Ico 0 T` (`mayer_identity_general_t_eventually`).
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` then gives agreement on all of `Ico 0 T`. -/
theorem polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {T : ℝ} (hT : 0 < T)
    (hkpT : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρT : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    polymerFreeEnergy G t = ∑' n : ℕ, mayerExpansionTerm G n t := by
  have hLHSan : AnalyticOnNhd ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ico 0 T) :=
    (polymerFreeEnergy_analyticOnNhd_Ici_zero G).mono Set.Ico_subset_Ici_self
  have hgAnIco : AnalyticOnNhd ℝ (fun t : ℝ => ∑' n : ℕ, mayerExpansionTerm G n t)
      (Set.Ico 0 T) :=
    polymerFreeEnergy_analyticOnNhd_mayer_tsum_Ico G hT hkpT hρT
  have heq : Set.EqOn (fun s : ℝ => polymerFreeEnergy G s)
      (fun t : ℝ => ∑' n : ℕ, mayerExpansionTerm G n t) (Set.Ico 0 T) :=
    hLHSan.eqOn_of_preconnected_of_eventuallyEq hgAnIco isPreconnected_Ico
      ⟨le_refl 0, hT⟩ (mayer_identity_general_t_eventually G)
  exact heq ht

end IsingModel
