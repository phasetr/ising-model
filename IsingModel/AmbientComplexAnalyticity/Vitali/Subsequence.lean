import IsingModel.AmbientComplexAnalyticity.Vitali.CompactGeometry

/-!
# Ambient Complex Analyticity Vitali Subsequence Bridge

Mechanical child split from `AmbientComplexAnalyticity/Vitali.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Subsequence local branch-family Vitali assembly

The actual Montel step is expected to produce a locally uniformly convergent
subsequence of local Lee-Yang logarithm branches. The next wrappers are the
subsequence-indexed variants of the preceding local branch-family handoffs:
the stage at branch-family index `m` is `σ m`, where `σ` is strictly
increasing. -/

/-- **Subsequence local branch-family Vitali bridge on a ball**: if a
Montel-extracted subsequence of per-stage branch witnesses is analytic on a
Lee-Yang ball and converges locally uniformly there, then its limit is
holomorphic on that ball. The branch identities are written at stage `σ m`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {σ : ℕ → ℕ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  IsingModel.vitali_bridge Metric.isOpen_ball
    (fun m => (hbranch m).1.differentiableOn) hconv

/-- **Subsequence local branch-family Vitali bridge with centre
identification**: for a ball centred at the real parameter `p.h`, a locally
uniform limit of subsequence branch witnesses is holomorphic on the ball and
agrees at the centre with the real infinite-volume free energy. The real-axis
convergence is composed with the strictly increasing index map `σ`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ F m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ (p.J : ℂ) (p.β : ℂ) hbranch hconv
  have hcenter : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) r := Metric.mem_ball_self hr
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hcenter
  have hbranch_eq :
      (fun m => F m (p.h : ℂ))
        = fun m => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    funext m
    exact (hbranch m).2.2
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  have hreal_subseq :
      Filter.Tendsto
        (fun m => freeEnergyComplexAlongExhaustion G Λ
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
        Filter.atTop
        (nhds ((freeEnergyInfinite G Λ p : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using hreal.comp hσ.tendsto_atTop
  exact ⟨hdiff, tendsto_nhds_unique hpoint hreal_subseq⟩

/-- **Subsequence local-cover branch-family Vitali bridge on
`leeYangDomain`**: if every Lee-Yang point has a ball on which a
subsequence-indexed branch family converges locally uniformly to the same
function `f`, then `f` is holomorphic on the whole Lee-Yang domain. This is
the handoff shape expected after a Montel diagonal extraction. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain := by
  intro h₀ hmem
  rcases hlocal h₀ hmem with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hdiff_ball :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β hbranch hconv
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- **Subsequence local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang cover of subsequence branch
families converging locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`, and at a real Lee-Yang centre it agrees with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ
                        (p.J : ℂ) z (p.β : ℂ) (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
      G Λ (p.J : ℂ) (p.β : ℂ) hlocal
  rcases hlocal (p.h : ℂ) hp with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hcenter :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      (V := V) G Λ p hBED hd hr hσ hbranch hconv
  exact ⟨hdiff, hcenter.2⟩


end Ambient

end IsingModel
