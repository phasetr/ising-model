import IsingModel.ClusterExpansion.MayerCore.CubicMayerClusterMontel
import IsingModel.ClusterExpansion.MayerCore.CubicMayerClusterRealAxis
import IsingModel.ComplexAnalyticity.Vitali
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Whole-sequence Montel/Vitali limit of the per-site complex cluster free energy (GJ §18.6)

This is PR-D2.3d of issue #4149 (§18.6), the analytic crux of the §18.6 finale.  We assemble the
three preceding sub-PRs into the **whole-sequence** locally uniform limit of the per-site complex
cluster free energy `cubicMayerClusterFreeEnergyComplex d n` over the cubic exhaustion of `ℤ^d`:

* D2.3a (`CubicMayerClusterFreeEnergyComplex.lean`): each `F_n` is `AnalyticOnNhd` on `ball 0 R`
  and uniformly norm-bounded there by `kpBound (2d) R`.
* D2.3b (`CubicMayerClusterMontel.lean`): the restrictions form a relatively compact family in the
  compact-open space `C(↑(ball 0 R), ℂ)` (Arzelà--Ascoli / Montel).
* D2.3c (`CubicMayerClusterRealAxis.lean`): on the real-axis segment `↑t`, `t ∈ Ioo 0 T`, the
  sequence converges to the real per-site infinite-volume cluster free energy
  `cubicInfiniteClusterFreeEnergyReal d t`.

The Montel carrier (D2.3b) gives one Montel-convergent subsequence with locally uniform limit
`f₀`, which is holomorphic (Vitali bridge) and matches `↑(cubicInfiniteClusterFreeEnergyReal d ·)`
on `Ioo 0 T`.  By the identity theorem any other Montel-convergent subsequence has the same
property, hence agrees with `f₀` on the segment, which accumulates at `↑t0 ∈ ball 0 R`, so the two
holomorphic limits are equal on the whole (preconnected) ball.  Uniqueness of every cluster point
upgrades the subsequence limit to whole-sequence convergence via
`IsCompact.tendsto_nhds_of_unique_mapClusterPt`, and the compact-open limit is converted back to
locally uniform convergence by the project bridge
`continuousMap_tendsto_compactOpen_to_tendstoLocallyUniformlyOn`.

## Main definitions and results

* `frequently_ofReal_Ioo_nhdsNE` — `↑t0` is an accumulation point of `ofReal '' Ioo 0 T`.
* `cubicMayerClusterFreeEnergyComplex_subseq_limit_analyticOnNhd` — any locally uniform subsequence
  limit is `AnalyticOnNhd ℂ` on `ball 0 R`.
* `cubicMayerClusterFreeEnergyComplex_subseq_limit_realAxis` — any locally uniform subsequence limit
  equals `↑(cubicInfiniteClusterFreeEnergyReal d ·)` on `Ioo 0 T`.
* `exists_cubicMayerClusterFreeEnergyComplex_limit` — the headline whole-sequence Montel/Vitali
  limit, holomorphic on `ball 0 R`, locally uniform along the whole sequence, with the prescribed
  real-axis values.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.6 (cluster expansion, analyticity).
-/

namespace IsingModel

open Filter Topology

/-- **Real-axis accumulation point for the identity theorem (GJ §18.6).**  For `t0 ∈ Ioo 0 T`, the
point `↑t0 : ℂ` is an accumulation point — along `𝓝[≠] ↑t0` the image
`(fun t : ℝ => (t : ℂ)) '' Ioo 0 T` is hit frequently.  Witnessed by the sequence
`u n := ↑(t0 + δ/(n+2))` with `δ := min t0 (T − t0) / 2 > 0`, which stays inside `Ioo 0 T`, differs
from `↑t0`, and tends to `↑t0`. -/
theorem frequently_ofReal_Ioo_nhdsNE {T t0 : ℝ} (ht0 : t0 ∈ Set.Ioo 0 T) :
    ∃ᶠ z in 𝓝[≠] ((t0 : ℝ) : ℂ),
      z ∈ (fun t : ℝ => (t : ℂ)) '' Set.Ioo 0 T := by
  rw [Set.mem_Ioo] at ht0
  obtain ⟨ht0pos, ht0lt⟩ := ht0
  set δ : ℝ := min t0 (T - t0) / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < min t0 (T - t0) := lt_min ht0pos (by linarith)
    positivity
  -- The witnessing real sequence and its complex image.
  set u : ℕ → ℝ := fun n => t0 + δ / (n + 2) with hudef
  set v : ℕ → ℂ := fun n => ((u n : ℝ) : ℂ) with hvdef
  -- Each `u n` lies in `Ioo 0 T`.
  have hδle1 : δ ≤ t0 := by
    have : min t0 (T - t0) ≤ t0 := min_le_left _ _
    rw [hδdef]; linarith
  have hδle2 : δ < T - t0 := by
    have : min t0 (T - t0) ≤ T - t0 := min_le_right _ _
    rw [hδdef]; linarith
  have hu_mem : ∀ n, u n ∈ Set.Ioo 0 T := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hfrac_pos : 0 < δ / ((n : ℝ) + 2) := by positivity
    have hfrac_le : δ / ((n : ℝ) + 2) ≤ δ := by
      rw [div_le_iff₀ hden]
      nlinarith [hδpos]
    refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
    · simp only [hudef]; linarith
    · simp only [hudef]; linarith
  -- Tendsto of the complex sequence to `↑t0`.
  have htend_real : Tendsto u atTop (𝓝 t0) := by
    have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := δ)).div_atTop hbase
    have := (tendsto_const_nhds (x := t0)).add h1
    simpa [hudef] using this
  have htend : Tendsto v atTop (𝓝 ((t0 : ℝ) : ℂ)) := by
    simpa [hvdef] using
      (Complex.continuous_ofReal.continuousAt.tendsto).comp htend_real
  -- Eventually `v n ≠ ↑t0` (since `u n ≠ t0`).
  have hne : ∀ᶠ n in atTop, v n ≠ ((t0 : ℝ) : ℂ) := by
    refine Eventually.of_forall (fun n => ?_)
    have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hpos : 0 < δ / ((n : ℝ) + 2) := by positivity
    have hune : u n ≠ t0 := by
      simp only [hudef]; intro h; nlinarith [hpos]
    simp only [hvdef]
    exact fun h => hune (Complex.ofReal_injective h)
  -- Tendsto into `𝓝[≠] ↑t0`, then frequently membership in the image.
  have htendNE : Tendsto v atTop (𝓝[≠] ((t0 : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, hne⟩
  have hfreq : ∃ᶠ n in atTop, v n ∈ (fun t : ℝ => (t : ℂ)) '' Set.Ioo 0 T := by
    refine Eventually.frequently (Eventually.of_forall (fun n => ?_))
    exact ⟨u n, hu_mem n, rfl⟩
  exact htendNE.frequently hfreq

/-- **Any locally uniform subsequence limit is holomorphic on the ball (GJ §18.6).**  If a
subsequence `F (σ m)` of the per-site complex cluster free energies converges locally uniformly on
`ball 0 R` to `f`, then `f` is `AnalyticOnNhd ℂ` there.  The stage functions are holomorphic
(D2.3a), so the Vitali bridge gives `DifferentiableOn`, upgraded to `AnalyticOnNhd` on the open
ball. -/
theorem cubicMayerClusterFreeEnergyComplex_subseq_limit_analyticOnNhd (d : ℕ) {R : ℝ} (hR : 0 < R)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun m z => cubicMayerClusterFreeEnergyComplex d (σ m) z) f atTop (Metric.ball (0 : ℂ) R)) :
    AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) R) :=
  (vitali_bridge Metric.isOpen_ball
    (fun m => (cubicMayerClusterFreeEnergyComplex_analyticOnNhd d (σ m) hR.le hkp2dR
      hρ2dR).differentiableOn) hconv).analyticOnNhd Metric.isOpen_ball

/-- **Any locally uniform subsequence limit matches the real limit on the segment (GJ §18.6).**  If
a subsequence `F (σ m)` (with `σ` strictly monotone) converges locally uniformly on `ball 0 R` to
`f`, then on the real-axis segment `Ioo 0 T` (with `T ≤ R`, `T ≤ 1`) the limit `f` equals the cast
of the real infinite-volume per-site cluster free energy `cubicInfiniteClusterFreeEnergyReal d t`.

Proof: for `t ∈ Ioo 0 T` the point `↑t` lies in `ball 0 R` (`|t| < T ≤ R`).  Locally uniform
convergence gives pointwise `F (σ m) ↑t → f ↑t`; the full sequence converges to
`↑(cubicInfiniteClusterFreeEnergyReal d t)` (D2.3c), so the subsequence does too
(`Tendsto.comp hσ.tendsto_atTop`); uniqueness of limits identifies the two. -/
theorem cubicMayerClusterFreeEnergyComplex_subseq_limit_realAxis (d : ℕ) {R T : ℝ}
    (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun m z => cubicMayerClusterFreeEnergyComplex d (σ m) z) f atTop (Metric.ball (0 : ℂ) R)) :
    ∀ t ∈ Set.Ioo 0 T, f (↑t) = ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ) := by
  intro t ht
  have htmem := Set.mem_Ioo.mp ht
  -- `↑t ∈ ball 0 R`.
  have hball : (↑t : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htmem.1]
    linarith [htmem.2]
  -- Subsequence pointwise convergence at `↑t`.
  have hsub : Tendsto (fun m => cubicMayerClusterFreeEnergyComplex d (σ m) (↑t)) atTop
      (𝓝 (f (↑t))) := hconv.tendsto_at hball
  -- Full-sequence convergence (D2.3c), restricted along `σ`.
  have hfull : Tendsto (fun n => cubicMayerClusterFreeEnergyComplex d n (↑t)) atTop
      (𝓝 ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ)) :=
    cubicMayerClusterFreeEnergyComplex_tendsto_realAxis d hT hT1 hkp2dT hρ2dT ht
  have hsub' : Tendsto (fun m => cubicMayerClusterFreeEnergyComplex d (σ m) (↑t)) atTop
      (𝓝 ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ)) :=
    hfull.comp hσ.tendsto_atTop
  exact tendsto_nhds_unique hsub hsub'

/-- **Whole-sequence Montel/Vitali limit of the per-site complex cluster free energy (GJ §18.6).**
Under the Kotecky--Preiss hypotheses at radius `R` (and the auxiliary radius `T ≤ R`, `T ≤ 1`),
there is a holomorphic `F_inf : ℂ → ℂ` on `ball 0 R` to which the **whole** sequence
`cubicMayerClusterFreeEnergyComplex d n` converges locally uniformly, and whose real-axis values on
`Ioo 0 T` are the cast of `cubicInfiniteClusterFreeEnergyReal d t`.

Proof outline.  Montel (D2.3b) supplies a compact carrier `A ⊆ C(↑(ball 0 R), ℂ)` and the
restriction sequence `Fc n` with `Fc n ∈ A`.  One Montel-convergent subsequence yields a locally
uniform limit `f₀ =: F_inf`, holomorphic (L1) and matching `↑(cubicInfiniteClusterFreeEnergyReal d
·)` on `Ioo 0 T` (L2).  For whole-sequence convergence we show every `MapClusterPt fc` of `Fc`
equals the compact-open limit `fc₀` of the chosen subsequence: a first-countable cluster point
gives a further subsequence `Fc ∘ ψ → fc`, which produces a holomorphic locally uniform limit `g`
agreeing with `fc` on the ball; both `g` and `f₀` are holomorphic and agree with
`↑(cubicInfiniteClusterFreeEnergyReal d ·)` on `Ioo 0 T`, hence agree frequently along `𝓝[≠] ↑t0`
(L0), so by the identity theorem they agree on the whole preconnected ball, forcing `fc = fc₀`.
`IsCompact.tendsto_nhds_of_unique_mapClusterPt` then gives whole-sequence compact-open convergence
`Fc → fc₀`, converted to locally uniform convergence by the project bridge. -/
theorem exists_cubicMayerClusterFreeEnergyComplex_limit
    (d : ℕ) {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    ∃ F_inf : ℂ → ℂ,
      DifferentiableOn ℂ F_inf (Metric.ball (0 : ℂ) R) ∧
      TendstoLocallyUniformlyOn (fun n z => cubicMayerClusterFreeEnergyComplex d n z) F_inf atTop
        (Metric.ball (0 : ℂ) R) ∧
      ∀ t ∈ Set.Ioo 0 T, F_inf (↑t) = ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ) := by
  classical
  -- First-countability of the compact-open continuous-map space on the (locally compact) ball.
  haveI : LocallyCompactSpace (↑(Metric.ball (0 : ℂ) R)) :=
    Metric.isOpen_ball.locallyCompactSpace
  haveI : FirstCountableTopology C(↑(Metric.ball (0 : ℂ) R), ℂ) := inferInstance
  -- Montel carrier (D2.3b).
  obtain ⟨A, hAcompact, Fc, hFc_mem, hFc_eq⟩ :=
    cubicMayerClusterFreeEnergyComplex_exists_compact_carrier d hR hkp2dR hρ2dR
  have hFc_eq' : ∀ n z (hz : z ∈ Metric.ball (0 : ℂ) R),
      cubicMayerClusterFreeEnergyComplex d n z = Fc n ⟨z, hz⟩ := hFc_eq
  -- The anchor accumulation point on the segment.
  set t0v : ℝ := T / 2 with ht0vdef
  have ht0mem : t0v ∈ Set.Ioo 0 T := Set.mem_Ioo.mpr ⟨by positivity, by linarith⟩
  -- Extract one Montel-convergent subsequence → `f₀ =: F_inf`.
  obtain ⟨σ₀, hσ₀, fc₀, f₀, hfc₀A, hf₀_agree, hconv₀⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball hAcompact hFc_mem hFc_eq'
  -- L1 / L2 for the chosen subsequence.
  have hf₀_analytic : AnalyticOnNhd ℂ f₀ (Metric.ball (0 : ℂ) R) :=
    cubicMayerClusterFreeEnergyComplex_subseq_limit_analyticOnNhd d hR hkp2dR hρ2dR hconv₀
  have hf₀_real : ∀ t ∈ Set.Ioo 0 T,
      f₀ (↑t) = ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ) :=
    cubicMayerClusterFreeEnergyComplex_subseq_limit_realAxis d hT hTR hT1 hkp2dT hρ2dT hσ₀ hconv₀
  -- The accumulation point `↑t0v` is in the ball.
  have ht0ball : (↑t0v : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0mem.1]
    linarith [ht0mem.2, hTR]
  -- Key uniqueness: every `MapClusterPt` of `Fc` equals `fc₀`.
  have huniq : ∀ fc ∈ A, MapClusterPt fc atTop Fc → fc = fc₀ := by
    intro fc hfcA hcluster
    -- A first-countable cluster point yields a convergent subsequence.
    obtain ⟨ψ, hψ, hψconv⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
    -- Build a total function `g` agreeing with `fc` on the ball.
    set g : ℂ → ℂ :=
      fun z => if hz : z ∈ Metric.ball (0 : ℂ) R then fc ⟨z, hz⟩ else 0 with hgdef
    have hg_agree : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) R), g z = fc ⟨z, hz⟩ := by
      intro z hz; rw [hgdef]; exact dif_pos hz
    -- Locally uniform convergence of the further subsequence to `g`.
    have hconv_g : TendstoLocallyUniformlyOn
        (fun m z => cubicMayerClusterFreeEnergyComplex d (ψ m) z) g atTop
        (Metric.ball (0 : ℂ) R) :=
      continuousMap_tendsto_compactOpen_to_tendstoLocallyUniformlyOn
        Metric.isOpen_ball (Fc := fun m => Fc (ψ m)) (fc := fc)
        (F := fun m z => cubicMayerClusterFreeEnergyComplex d (ψ m) z) (f := g)
        (fun m z hz => hFc_eq (ψ m) z hz) hg_agree
        (by simpa [Function.comp_def] using hψconv)
    -- L1 / L2 for `g`.
    have hg_analytic : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) :=
      cubicMayerClusterFreeEnergyComplex_subseq_limit_analyticOnNhd d hR hkp2dR hρ2dR hconv_g
    have hg_real : ∀ t ∈ Set.Ioo 0 T,
        g (↑t) = ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ) :=
      cubicMayerClusterFreeEnergyComplex_subseq_limit_realAxis d hT hTR hT1 hkp2dT hρ2dT hψ hconv_g
    -- `g` and `f₀` agree frequently along `𝓝[≠] ↑t0v`.
    have hfreq_eq : ∃ᶠ z in 𝓝[≠] ((t0v : ℝ) : ℂ), g z = f₀ z := by
      refine (frequently_ofReal_Ioo_nhdsNE ht0mem).mono ?_
      rintro z ⟨t, ht, rfl⟩
      rw [hg_real t ht, hf₀_real t ht]
    -- Identity theorem on the preconnected ball.
    have hEqOn : Set.EqOn g f₀ (Metric.ball (0 : ℂ) R) :=
      hg_analytic.eqOn_of_preconnected_of_frequently_eq hf₀_analytic
        Metric.isPreconnected_ball ht0ball hfreq_eq
    -- Transfer ball-equality of `g, f₀` to continuous-map equality of `fc, fc₀`.
    refine ContinuousMap.ext (fun z => ?_)
    have hzmem : (z : ℂ) ∈ Metric.ball (0 : ℂ) R := z.2
    have := hEqOn hzmem
    rw [hg_agree (z : ℂ) hzmem, hf₀_agree (z : ℂ) hzmem] at this
    simpa using this
  -- Whole-sequence compact-open convergence.
  have hwhole : Tendsto Fc atTop (𝓝 fc₀) :=
    hAcompact.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hFc_mem) huniq
  -- Convert to locally uniform convergence of the whole sequence.
  have hconvWhole : TendstoLocallyUniformlyOn
      (fun n z => cubicMayerClusterFreeEnergyComplex d n z) f₀ atTop
      (Metric.ball (0 : ℂ) R) :=
    continuousMap_tendsto_compactOpen_to_tendstoLocallyUniformlyOn
      Metric.isOpen_ball (Fc := Fc) (fc := fc₀)
      (F := fun n z => cubicMayerClusterFreeEnergyComplex d n z) (f := f₀)
      hFc_eq' hf₀_agree hwhole
  refine ⟨f₀, ?_, hconvWhole, hf₀_real⟩
  exact hf₀_analytic.differentiableOn

end IsingModel
