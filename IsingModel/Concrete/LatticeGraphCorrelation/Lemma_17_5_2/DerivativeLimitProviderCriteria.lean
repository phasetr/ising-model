import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.DerivativeLimitProvider
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# GJ §17.5 Lemma 17.5.2 capstone — derivative-limit provider criteria

This module records Dini-style sufficient criteria for the
`Lemma_17_5_2_DerivativeLimitProvider` input.  The criteria reduce the provider
proof to pointwise convergence of the finite-volume beta-derivative profiles
plus either a monotonicity direction and continuity of the limiting derivative
profile, compact-uniform Cauchy control plus pointwise convergence, or
closed-interval metric Cauchy control alone.  In the last case, completeness of
`ℝ` constructs the pointwise derivative-profile limit.  A further pair of
criteria discharges that closed-interval metric Cauchy control from a concrete
convergence-rate bound on consecutive finite-volume stages: a summable bound on
the consecutive-stage derivative differences (telescoping/summable-tail), and
its geometric specialization matching cluster-expansion convergence rates.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof and
  Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider extraction, closed
interval form**: a provider gives a limiting derivative profile whose
finite-volume beta-derivative profiles converge uniformly on every closed
interval contained in the open high-temperature region.

This is the direct closed-interval consequence of the locally uniform provider
and is the form consumed by compact-Cauchy and finite-HLS follow-up arguments.
-/
theorem lemma_17_5_2_derivative_limit_provider_tendstoUniformlyOn_Icc
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} {x z : Fin d → ℤ}
    {β₁ β₂ : ℝ}
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ∃ g' : ℝ → ℝ,
      TendstoUniformlyOn
        (fun n β =>
          deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
        g' Filter.atTop (Set.Icc β₁ β₂) := by
  obtain ⟨g', hloc⟩ := hprovider
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo] at hloc
  exact ⟨g', hloc (Set.Icc β₁ β₂) hIcc isCompact_Icc⟩

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider extraction, uniform
Cauchy form**: on every closed beta interval inside the high-temperature
region, a derivative-limit provider makes the finite-volume derivative
profiles uniformly Cauchy.

This exposes the provider as exactly the compact-Cauchy datum used by the
closed-interval Cauchy route, without requiring downstream callers to unpack
the limiting derivative profile. -/
theorem lemma_17_5_2_derivative_limit_provider_uniformCauchySeqOn_Icc
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} {x z : Fin d → ℤ}
    {β₁ β₂ : ℝ}
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    UniformCauchySeqOn
      (fun n β =>
        deriv (fun β' =>
          Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
      Filter.atTop (Set.Icc β₁ β₂) := by
  obtain ⟨_, htend⟩ :=
    lemma_17_5_2_derivative_limit_provider_tendstoUniformlyOn_Icc
      (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) hprovider hIcc
  exact htend.uniformCauchySeqOn

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider extraction, metric
Cauchy form**: an epsilon--`N` restatement of the preceding uniform-Cauchy
closed-interval consequence.

This is deliberately aligned with
`Lemma_17_5_2_DerivativeProfileMetricCauchyOnIcc`, while avoiding a reverse
import from the provider module to the named-input module. -/
theorem lemma_17_5_2_derivative_limit_provider_metricCauchy_on_Icc
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    {J : ℝ} {x z : Fin d → ℤ}
    {β₁ β₂ : ℝ}
    (hprovider : Lemma_17_5_2_DerivativeLimitProvider Λ J x z)
    (hIcc : Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ β ∈ Set.Icc β₁ β₂,
        dist
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
          (deriv (fun β' =>
            Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε := by
  have hcauchy :=
    lemma_17_5_2_derivative_limit_provider_uniformCauchySeqOn_Icc
      (Λ := Λ) (J := J) (x := x) (z := z)
      (β₁ := β₁) (β₂ := β₂) hprovider hIcc
  exact Metric.uniformCauchySeqOn_iff.mp hcauchy

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
compact-uniform Cauchy form**: if the finite-volume beta-derivative profiles
are uniformly Cauchy on every compact subset of the open high-temperature
interval, and they converge pointwise to `g'`, then they converge locally
uniformly there and hence supply the derivative-limit provider. -/
theorem lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_compacts
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcauchy :
      ∀ K : Set ℝ,
        K ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          IsCompact K →
            UniformCauchySeqOn
              (fun n β =>
                deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
              Filter.atTop K)
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioo]
  intro K hK_sub hK_compact
  exact (hcauchy K hK_sub hK_compact).tendstoUniformlyOn_of_tendsto
    fun β hβ => hpoint β (hK_sub hβ)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
metric compact Cauchy form**: an epsilon--eventual version of
`lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_compacts`. -/
theorem lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_compacts
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcauchy :
      ∀ K : Set ℝ,
        K ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          IsCompact K →
            ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ β ∈ K,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine
    lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_compacts
      Λ J x z g' ?_ hpoint
  intro K hK_sub hK_compact
  exact Metric.uniformCauchySeqOn_iff.2 (hcauchy K hK_sub hK_compact)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
closed-interval Cauchy form**: it is enough to prove uniform Cauchy control of
the finite-volume beta-derivative profiles on every closed interval contained
in the open high-temperature interval, together with pointwise convergence on
the open interval. -/
theorem lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcauchy :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          UniformCauchySeqOn
            (fun n β =>
              deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
            Filter.atTop (Set.Icc β₁ β₂))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro β hβ
  let B : ℝ := 1 / (J * ↑(2 * d))
  let β₁ : ℝ := β / 2
  let β₂ : ℝ := (β + B) / 2
  have hβ₁β : β₁ < β := by
    dsimp [β₁]
    linarith [hβ.1]
  have hββ₂ : β < β₂ := by
    dsimp [β₂, B]
    linarith [hβ.2]
  have hIcc :
      Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := by
    intro γ hγ
    have hβ₁_pos : 0 < β₁ := by
      dsimp [β₁]
      linarith [hβ.1]
    have hβ₂_lt : β₂ < B := by
      dsimp [β₂, B]
      linarith [hβ.2]
    exact ⟨lt_of_lt_of_le hβ₁_pos hγ.1, lt_of_le_of_lt hγ.2 hβ₂_lt⟩
  refine ⟨Set.Icc β₁ β₂, nhdsWithin_le_nhds (Icc_mem_nhds hβ₁β hββ₂), ?_⟩
  exact (hcauchy β₁ β₂ hIcc).tendstoUniformlyOn_of_tendsto
    fun γ hγ => hpoint γ (hIcc hγ)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
metric closed-interval Cauchy form**: an epsilon--eventual version of
`lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_Icc`. -/
theorem lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcauchy :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc β₁ β₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε)
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine
    lemma_17_5_2_derivative_limit_provider_of_uniformCauchy_on_Icc
      Λ J x z g' ?_ hpoint
  intro β₁ β₂ hIcc
  exact Metric.uniformCauchySeqOn_iff.2 (hcauchy β₁ β₂ hIcc)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
metric closed-interval Cauchy form with constructed pointwise limit**: closed
interval metric Cauchy control alone supplies the derivative-limit provider.

For each beta in the open high-temperature interval, the closed-interval Cauchy
input gives a Cauchy sequence of finite-volume derivative values at that beta;
completeness of `ℝ` supplies its pointwise limit.  The existing
closed-interval Cauchy criterion then upgrades those pointwise limits to local
uniform convergence. -/
theorem lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc_complete
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ)
    (hcauchy :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            ∀ β ∈ Set.Icc β₁ β₂,
              dist
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} m) β)
                (deriv (fun β' =>
                  Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β) < ε) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  let F : ℕ → ℝ → ℝ := fun n β =>
    deriv (fun β' =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β
  have hpoint_exists :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        ∃ gβ : ℝ, Filter.Tendsto (fun n => F n β) Filter.atTop (nhds gβ) := by
    intro β hβ
    let B : ℝ := 1 / (J * ↑(2 * d))
    let β₁ : ℝ := β / 2
    let β₂ : ℝ := (β + B) / 2
    have hβ₁β : β₁ < β := by
      dsimp [β₁]
      linarith [hβ.1]
    have hββ₂ : β < β₂ := by
      dsimp [β₂, B]
      linarith [hβ.2]
    have hβ_mem : β ∈ Set.Icc β₁ β₂ := ⟨hβ₁β.le, hββ₂.le⟩
    have hIcc :
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) := by
      intro γ hγ
      have hβ₁_pos : 0 < β₁ := by
        dsimp [β₁]
        linarith [hβ.1]
      have hβ₂_lt : β₂ < B := by
        dsimp [β₂, B]
        linarith [hβ.2]
      exact ⟨lt_of_lt_of_le hβ₁_pos hγ.1, lt_of_le_of_lt hγ.2 hβ₂_lt⟩
    have huc :
        UniformCauchySeqOn F Filter.atTop (Set.Icc β₁ β₂) := by
      exact Metric.uniformCauchySeqOn_iff.2 (by simpa [F] using hcauchy β₁ β₂ hIcc)
    exact cauchySeq_tendsto_of_complete (huc.cauchySeq hβ_mem)
  let g' : ℝ → ℝ := fun β =>
    if hβ : β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) then
      Classical.choose (hpoint_exists β hβ)
    else 0
  have hg' :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto (fun n => F n β) Filter.atTop (nhds (g' β)) := by
    intro β hβ
    have hchosen := (Classical.choose_spec (hpoint_exists β hβ))
    have hgeq :
        g' β = Classical.choose (hpoint_exists β hβ) := by
      exact dif_pos hβ
    simpa [hgeq] using hchosen
  exact
    lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc
      Λ J x z g' hcauchy (by
        intro β hβ
        simpa [F] using hg' β hβ)

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
summable-increment form**: if there is a summable sequence `c : ℕ → ℝ` such
that on every closed interval inside the open high-temperature region the
consecutive-stage finite-volume beta-derivative differences are uniformly
bounded by `c k`, then the finite-volume derivative profiles are uniformly
Cauchy on each such interval, and completeness of `ℝ` supplies the
derivative-limit provider.

The proof is a telescoping/summable-tail argument: on a fixed closed interval
the polygon inequality `dist_le_Ico_sum_of_dist_le` bounds `dist (F m β) (F n β)`
by `∑_{Ico m n} c`, which equals the difference of partial sums of `c`; since
`c` is summable, the partial sums form a Cauchy sequence, so that difference is
below any `ε` uniformly in `β` once both indices are large.  This packages the
remaining derivative-limit input as a concrete convergence-rate hypothesis. -/
theorem lemma_17_5_2_derivative_limit_provider_of_summable_increments
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (c : ℕ → ℝ) (hc : Summable c)
    (hincr :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ∀ β ∈ Set.Icc β₁ β₂,
            dist
              (deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
              (deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤ c k) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  -- The partial sums of `c` form a Cauchy sequence by summability.
  have hScauchy :
      CauchySeq (fun N => ∑ i ∈ Finset.range N, c i) :=
    hc.hasSum.tendsto_sum_nat.cauchySeq
  apply lemma_17_5_2_derivative_limit_provider_of_metricCauchy_on_Icc_complete
  intro β₁ β₂ hIcc ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hScauchy ε hε
  refine ⟨N, fun m hm n hn β hβ => ?_⟩
  -- Abbreviate the stagewise derivative profile at the fixed point `β`.
  set f : ℕ → ℝ := fun k =>
    deriv (fun β' =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β with hf
  -- A monotone-index estimate, then symmetrize.
  have hbound :
      ∀ p q : ℕ, p ≤ q → N ≤ p → N ≤ q → dist (f p) (f q) < ε := by
    intro p q hpq hNp hNq
    calc
      dist (f p) (f q)
          ≤ ∑ i ∈ Finset.Ico p q, c i :=
            dist_le_Ico_sum_of_dist_le hpq fun {k} _ _ => hincr β₁ β₂ hIcc k β hβ
      _ = (∑ i ∈ Finset.range q, c i) - ∑ i ∈ Finset.range p, c i :=
            Finset.sum_Ico_eq_sub c hpq
      _ ≤ |(∑ i ∈ Finset.range q, c i) - ∑ i ∈ Finset.range p, c i| :=
            le_abs_self _
      _ = dist (∑ i ∈ Finset.range q, c i) (∑ i ∈ Finset.range p, c i) :=
            (Real.dist_eq _ _).symm
      _ < ε := hN q hNq p hNp
  rcases le_total m n with hmn | hnm
  · exact hbound m n hmn hm hn
  · simpa [dist_comm] using hbound n m hnm hn hm

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
geometric-increment form**: the special case of
`lemma_17_5_2_derivative_limit_provider_of_summable_increments` in which the
consecutive-stage finite-volume beta-derivative differences are bounded by a
geometric sequence `M · ratio ^ k` with `0 ≤ ratio < 1`.

This matches the geometric (exponential) finite-to-infinite convergence rate
produced by cluster-expansion estimates: the geometric series is summable, so
the summable-increment criterion applies directly. -/
theorem lemma_17_5_2_derivative_limit_provider_of_geometric_increments
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (M ratio : ℝ)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (hincr :
      ∀ β₁ β₂ : ℝ,
        Set.Icc β₁ β₂ ⊆ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))) →
          ∀ k : ℕ, ∀ β ∈ Set.Icc β₁ β₂,
            dist
              (deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} k) β)
              (deriv (fun β' =>
                Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} (k + 1)) β) ≤
              M * ratio ^ k) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  have hsummable : Summable (fun k => M * ratio ^ k) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left M
  exact lemma_17_5_2_derivative_limit_provider_of_summable_increments
    Λ J x z (fun k => M * ratio ^ k) hsummable hincr

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
monotone form**: pointwise convergence of the finite-volume beta-derivative
profiles to a continuous limit upgrades to locally uniform convergence by
Dini's theorem when the profiles are stagewise monotone increasing on the
open high-temperature interval. -/
theorem lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcont :
      ∀ n,
        ContinuousOn
          (fun β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hmono :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Monotone
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β))
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  exact Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
    hcont hmono hg_cont hpoint

/-- **GJ §17.5 Lemma 17.5.2 derivative-limit provider criterion,
antitone form**: the decreasing-profile analogue of
`lemma_17_5_2_derivative_limit_provider_of_monotone_deriv_profiles`. -/
theorem lemma_17_5_2_derivative_limit_provider_of_antitone_deriv_profiles
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J : ℝ) (x z : Fin d → ℤ) (g' : ℝ → ℝ)
    (hcont :
      ∀ n,
        ContinuousOn
          (fun β =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hanti :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Antitone
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β))
    (hg_cont : ContinuousOn g' (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))))
    (hpoint :
      ∀ β ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d))),
        Filter.Tendsto
          (fun n =>
            deriv (fun β' =>
              Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β'⟩ : IsingParams ℝ) {x, z} n) β)
          Filter.atTop (nhds (g' β))) :
    Lemma_17_5_2_DerivativeLimitProvider Λ J x z := by
  refine ⟨g', ?_⟩
  exact Antitone.tendstoLocallyUniformlyOn_of_forall_tendsto
    hcont hanti hg_cont hpoint

end Ambient
end IsingModel
