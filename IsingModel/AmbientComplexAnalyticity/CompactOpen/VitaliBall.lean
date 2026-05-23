import IsingModel.AmbientComplexAnalyticity.Vitali

/-!
# Ambient compact-open extraction split — compact-open Vitali bridges on balls

Part of the split ambient compact-open layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Compact-open extraction handoff on Lee-Yang balls

The previous subsequence handoffs start after a locally uniformly convergent
subsequence of branch witnesses has already been selected. The next wrappers
package the standard topological extraction step available once the local
branch witnesses are known to lie in a compact subset of the compact-open
function space on a ball. This still does not prove Montel compactness of the
branch family; compactness is an explicit hypothesis. -/

/-- **Compact-open extraction plus subsequence Vitali bridge on a ball**:
if a local branch family on a ball is represented by continuous maps whose
range lies in a compact subset of `C(ball, ℂ)`, then a subsequence converges
locally uniformly on the ball and its limit is holomorphic there. This is the
post-Montel compactness-to-Vitali handoff. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball h₀ r, ℂ)}
    {Fc : ℕ → C(Metric.ball h₀ r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball h₀ r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball h₀ r, ℂ),
          fc ∈ A ∧ ∀ z (hz : z ∈ Metric.ball h₀ r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball h₀ r) ∧
        DifferentiableOn ℂ f (Metric.ball h₀ r) := by
  haveI : LocallyCompactSpace (Metric.ball h₀ r) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball hA hFc_mem hFres with
    ⟨σ, hσ, fc, f, hfcA, hf_agree, hconv⟩
  have hbranch_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F (σ m) z) m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F (σ m) z) m h₀
            = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m) := by
    intro m
    simpa using hbranch (σ m)
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch_sub hconv
  exact ⟨σ, hσ, f, ⟨fc, hfcA, hf_agree⟩, hconv, hdiff⟩

/-- **Compact-open extraction plus subsequence Vitali bridge with centre
identification**: for a ball centred at a real Lee-Yang parameter, compactness
of the branch family in the compact-open topology yields a locally uniformly
convergent subsequence; the PR #2693 subsequence handoff makes the limit
holomorphic and identifies its centre value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ}
    {A : Set C(Metric.ball (p.h : ℂ) r, ℂ)}
    {Fc : ℕ → C(Metric.ball (p.h : ℂ) r, ℂ)}
    (hA : IsCompact A)
    (hFc_mem : ∀ n, Fc n ∈ A)
    (hFres : ∀ n z (hz : z ∈ Metric.ball (p.h : ℂ) r),
      F n z = Fc n ⟨z, hz⟩)
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (p.h : ℂ) r, ℂ),
          fc ∈ A ∧
            ∀ z (hz : z ∈ Metric.ball (p.h : ℂ) r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball (p.h : ℂ) r) ∧
        DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
        f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  haveI : LocallyCompactSpace (Metric.ball (p.h : ℂ) r) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball hA hFc_mem hFres with
    ⟨σ, hσ, fc, f, hfcA, hf_agree, hconv⟩
  have hbranch_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F (σ m) z) m)
          (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ (fun m z => F (σ m) z) m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    intro m
    simpa using hbranch (σ m)
  have hcenter :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr hσ hbranch_sub hconv
  exact ⟨σ, hσ, f, ⟨fc, hfcA, hf_agree⟩, hconv, hcenter.1, hcenter.2⟩

/-- **Two-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: if branch families on two Lee-Yang balls are represented by
continuous maps whose ranges lie in compact subsets of the corresponding
compact-open function spaces, then a single strictly increasing subsequence can
be chosen so that both branch families converge locally uniformly on their
balls and both limits are holomorphic there. This is the two-ball base case for
finite local-cover diagonal extraction; it does not assert overlap
compatibility of the two limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h01 h02 : ℂ} {r1 r2 : ℝ}
    {F1 F2 : ℕ → ℂ → ℂ}
    {A1 : Set C(Metric.ball h01 r1, ℂ)}
    {A2 : Set C(Metric.ball h02 r2, ℂ)}
    {Fc1 : ℕ → C(Metric.ball h01 r1, ℂ)}
    {Fc2 : ℕ → C(Metric.ball h02 r2, ℂ)}
    (hA1 : IsCompact A1) (hA2 : IsCompact A2)
    (hFc1_mem : ∀ n, Fc1 n ∈ A1)
    (hFc2_mem : ∀ n, Fc2 n ∈ A2)
    (hFres1 : ∀ n z (hz : z ∈ Metric.ball h01 r1),
      F1 n z = Fc1 n ⟨z, hz⟩)
    (hFres2 : ∀ n z (hz : z ∈ Metric.ball h02 r2),
      F2 n z = Fc2 n ⟨z, hz⟩)
    (hbranch1 : ∀ n,
      AnalyticOnNhd ℂ (F1 n) (Metric.ball h01 r1)
        ∧ (∀ z ∈ Metric.ball h01 r1,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F1 n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F1 n h01 = freeEnergyComplexAlongExhaustion G Λ J h01 β n)
    (hbranch2 : ∀ n,
      AnalyticOnNhd ℂ (F2 n) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F2 n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F2 n h02 = freeEnergyComplexAlongExhaustion G Λ J h02 β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∃ f1 : ℂ → ℂ,
        (∃ fc1 : C(Metric.ball h01 r1, ℂ),
          fc1 ∈ A1 ∧ ∀ z (hz : z ∈ Metric.ball h01 r1), f1 z = fc1 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F1 (σ m) z) f1 Filter.atTop (Metric.ball h01 r1) ∧
        DifferentiableOn ℂ f1 (Metric.ball h01 r1)) ∧
      (∃ f2 : ℂ → ℂ,
        (∃ fc2 : C(Metric.ball h02 r2, ℂ),
          fc2 ∈ A2 ∧ ∀ z (hz : z ∈ Metric.ball h02 r2), f2 z = fc2 ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F2 (σ m) z) f2 Filter.atTop (Metric.ball h02 r2) ∧
        DifferentiableOn ℂ f2 (Metric.ball h02 r2)) := by
  haveI : LocallyCompactSpace (Metric.ball h01 r1) :=
    Metric.isOpen_ball.locallyCompactSpace
  haveI : LocallyCompactSpace (Metric.ball h02 r2) :=
    Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_two_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      Metric.isOpen_ball Metric.isOpen_ball hA1 hA2 hFc1_mem hFc2_mem
      hFres1 hFres2 with
    ⟨σ, hσ, hlim1, hlim2⟩
  rcases hlim1 with ⟨fc1, f1, hfc1A, hf1_agree, hconv1⟩
  rcases hlim2 with ⟨fc2, f2, hfc2A, hf2_agree, hconv2⟩
  have hbranch1_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F1 (σ m) z) m) (Metric.ball h01 r1)
        ∧ (∀ z ∈ Metric.ball h01 r1,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F1 (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F1 (σ m) z) m h01
            = freeEnergyComplexAlongExhaustion G Λ J h01 β (σ m) := by
    intro m
    simpa using hbranch1 (σ m)
  have hbranch2_sub : ∀ m,
      AnalyticOnNhd ℂ ((fun m z => F2 (σ m) z) m) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                (fun m z => F2 (σ m) z) m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ (fun m z => F2 (σ m) z) m h02
            = freeEnergyComplexAlongExhaustion G Λ J h02 β (σ m) := by
    intro m
    simpa using hbranch2 (σ m)
  have hdiff1 :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch1_sub hconv1
  have hdiff2 :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β (σ := σ) hbranch2_sub hconv2
  exact ⟨σ, hσ,
    ⟨f1, ⟨fc1, hfc1A, hf1_agree⟩, hconv1, hdiff1⟩,
    ⟨f2, ⟨fc2, hfc2A, hf2_agree⟩, hconv2, hdiff2⟩⟩


end Ambient
end IsingModel
