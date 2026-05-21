import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches

/-!
# ℤ^d subsequence compact-open and finite-cover wrappers

Mechanical child split from `PerStageComplex.lean`.
-/

namespace IsingModel
namespace Ambient

/-! #### Subsequence local branch-family Vitali assembly -/

/-- **ℤ^d subsequence local branch-family Vitali bridge on a ball**:
if a Montel-extracted subsequence of per-stage branch witnesses is analytic on
a ball and converges locally uniformly there, then its limit is holomorphic on
that ball. The branch identities are written at stage `σ m`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {σ : ℕ → ℕ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β (σ m))
        ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hbranch hconv

/-- **ℤ^d subsequence local branch-family Vitali bridge with centre
identification**: for a ball centred at the real parameter `p.h`, a locally
uniform limit of subsequence branch witnesses is holomorphic on the ball and
agrees at the centre with the real infinite-volume free energy. -/
theorem
freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {r : ℝ} (hr : 0 < r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ F m (p.h : ℂ) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
    (IsingModel.latticeGraph d) Λ p hBED hd hr hσ hbranch hconv

/-- **ℤ^d subsequence local-cover branch-family Vitali bridge on
`leeYangDomain`**: if every Lee-Yang point has a ball on which a
subsequence-indexed branch family converges locally uniformly to the same
`f`, then `f` is holomorphic on the whole Lee-Yang domain. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ J z β (σ m))
              ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J h₀ β (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
    (IsingModel.latticeGraph d) Λ J β hlocal

/-- **ℤ^d subsequence local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang cover of subsequence branch
families converging locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`, and at a real Lee-Yang centre it agrees with
`↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
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
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ
                        (p.J : ℂ) z (p.β : ℂ) (σ m))
              ∧ F m h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hσ hp hlocal

/-- **ℤ^d compact-open extraction plus subsequence Vitali bridge on a ball**:
if local branch witnesses on a ball are represented by continuous maps in a
compact subset of the compact-open function space, then a subsequence
converges locally uniformly and its limit is holomorphic on the ball. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
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
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h₀ β n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball h₀ r, ℂ),
          fc ∈ A ∧ ∀ z (hz : z ∈ Metric.ball h₀ r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball h₀ r) ∧
        DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_bridge_ball
    (IsingModel.latticeGraph d) Λ J β hA hFc_mem hFres hbranch

/-- **ℤ^d compact-open extraction plus subsequence Vitali bridge with centre
identification**: for a ball centred at a real Lee-Yang parameter, compact-open
compactness of the branch family yields a locally uniformly convergent
subsequence whose limit is holomorphic and agrees at the centre with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
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
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (p.h : ℂ) r, ℂ),
          fc ∈ A ∧
            ∀ z (hz : z ∈ Metric.ball (p.h : ℂ) r), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F (σ m) z) f Filter.atTop (Metric.ball (p.h : ℂ) r) ∧
        DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
        f (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_ball_real
    (IsingModel.latticeGraph d) Λ p hBED hd hr hA hFc_mem hFres hbranch

/-- **ℤ^d two-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: compact-open compactness on two Lee-Yang balls gives one common
subsequence, locally uniform convergence on both balls, and holomorphic limits
on both balls. This does not assert overlap compatibility of the two limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
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
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F1 n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F1 n h01 = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h01 β n)
    (hbranch2 : ∀ n,
      AnalyticOnNhd ℂ (F2 n) (Metric.ball h02 r2)
        ∧ (∀ z ∈ Metric.ball h02 r2,
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F2 n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n)
        ∧ F2 n h02 = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J h02 β n) :
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
        DifferentiableOn ℂ f2 (Metric.ball h02 r2)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_two_ball
    (IsingModel.latticeGraph d) Λ J β hA1 hA2 hFc1_mem hFc2_mem
    hFres1 hFres2 hbranch1 hbranch2

/-- **ℤ^d finite-ball compact-open diagonal extraction plus subsequence Vitali
bridge**: compact-open compactness on finitely many Lee-Yang balls gives one
common subsequence, locally uniform convergence on every ball, and holomorphic
limits on every ball. This does not assert overlap compatibility of the local
limits. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
          fc ∈ A i ∧
            ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F i (σ m) z) f Filter.atTop (Metric.ball (h0 i) (r i)) ∧
        DifferentiableOn ℂ f (Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch

/-- **ℤ^d finite-ball compact-open diagonal extraction with overlap
compatibility**: if the stage branches in the finite-ball compact-open handoff
are eventually equal on every pairwise overlap, the extracted holomorphic local
limits are pairwise equal on those overlaps. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_fin_ball_overlap_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d packaged finite compact-open subsequence branch-limit family**:
compact-open compactness on finitely many balls, plus eventual stage-level
overlap equality, produces a structured finite subsequence branch-limit
family. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    Nonempty (Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n h0 r) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite compact-open
subsequence package**: restricts pre-Montel all-stage branch choices to
finitely many Lee-Yang centres, then applies the ambient finite compact-open
diagonal handoff under compact-open compactness and explicit eventual overlap
equality. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n
      (fun i => (center i : ℂ))
      (fun i => data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d packaged finite subsequence branch-limit patching**: a compatible
`Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches to one function
differentiable on the finite union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n h0 r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    (IsingModel.latticeGraph d) Λ J β n family

/-- **ℤ^d packaged finite subsequence branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field `p.h`,
then a compatible `Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches on the
finite union of balls and the patched value at the real centre agrees with
`↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n h0 r)
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n family i₀ hcenter hr

/-- **ℤ^d finite Lee-Yang cover branch-limit patching**: a compatible finite
Lee-Yang cover package patches to one differentiable function on the finite
union of its Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
    (IsingModel.latticeGraph d) Λ J β n cover

/-- **ℤ^d finite Lee-Yang cover branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field `p.h`,
the finite-union patch agrees there with `↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n center r)
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n cover i₀ hcenter

/-- **ℤ^d finite real-centred Lee-Yang cover branch-limit patching**: a finite
Lee-Yang cover package with a bundled real-centre index patches to one
differentiable function on the finite union, with value
`↑Ambient.freeEnergyInfinite` at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g
        (⋃ i : Fin n,
          Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n realCover

/-- **ℤ^d compact finite real-centred Lee-Yang cover patching**: a compact
target set covered by a finite real-centred Lee-Yang cover inherits the
finite-cover patch, restricted to differentiability on the compact target,
while preserving the real-centre identification. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    (compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p K n center r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_compactFiniteRealCover_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n compactCover

/-- **ℤ^d finite compact-open extraction to a patched finite family**:
compact-open compactness on finitely many balls and eventual stage-level
overlap equality produce both a packaged finite subsequence branch-limit family
and a patched function on the finite union of balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCompactOpenBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β m)
        ∧ F i m (h0 i) = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch
    (IsingModel.latticeGraph d) Λ J β n hA hFc_mem hFres hbranch hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite compact-open patch**:
restricts pre-Montel all-stage branch choices to finitely many Lee-Yang
centres, builds the finite compact-open subsequence package, and patches the
compatible local limits on the finite union of selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n
        (fun i => (center i : ℂ))
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen_patch
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover
package**: restricts pre-Montel all-stage branch choices to finitely many
Lee-Yang centres, then packages the finite compact-open subsequence extraction
as a finite Lee-Yang cover branch-limit family. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center
      (fun i => data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover patch**:
restricts pre-Montel all-stage branch choices to finitely many Lee-Yang
centres, builds the finite Lee-Yang cover package, and patches the compatible
local limits on the finite union of selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage data to finite real-centred
Lee-Yang cover patch**: restricts all-stage branch choices to finitely many
Lee-Yang centres and uses a selected real-centre index to identify the patched
value with `↑Ambient.freeEnergyInfinite`. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n center data hA hFc_mem hFres
    hoverlap i₀ hcenter

/-- **ℤ^d pointwise-normalised all-stage data to compact real-centred
Lee-Yang cover patch**: for a compact target covered by finitely many selected
all-stage Lee-Yang balls, produces the compact finite real-centred cover
package and a patch differentiable on the compact target. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball (center i : ℂ) (data.branchData.radius (center i)))
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n center data hK hKsub hpK
    hKcover hA hFc_mem hFres hoverlap i₀ hcenter

/-- **ℤ^d compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts finitely many all-stage Lee-Yang balls
covering `K`, with a selected centre at the real field. -/
theorem
    exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data) :=
  Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage compact finite geometry to compact
real-cover patch**: feeds compactness-extracted all-stage centres into the
compact real-cover patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStage_compactRealCOpen_patch_geom_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    {A : ∀ i : Fin geom.n,
      Set C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    {Fc : ∀ i : Fin geom.n, ℕ →
      C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      data.branchData.branchFamily (geom.center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
          ∩ Metric.ball (geom.center j : ℂ)
            (data.branchData.radius (geom.center j)))) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    (IsingModel.latticeGraph d) Λ p hBED hd data geom hA hFc_mem hFres hoverlap

/-- **ℤ^d pointwise-normalised all-stage compact-open data to compact
real-cover patch**: packaged compact-open data for the selected all-stage
geometry feeds the compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (cOpen : Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
      (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom cOpen

/-- **ℤ^d compact target to packaged all-stage compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, and packaged
compact-open data then yields the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

end Ambient

end IsingModel
