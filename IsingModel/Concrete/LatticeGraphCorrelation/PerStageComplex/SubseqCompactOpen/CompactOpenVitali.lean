import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches

/-!
# Per-stage complex analyticity wrappers: CompactOpenVitali

Consolidated `CompactOpenVitali` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# SubseqCompactOpen split — subsequence Vitali ball wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — subsequence Vitali local-cover wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — subsequence Vitali assembly

Compatibility module re-exporting the subsequence Vitali child modules.
-/

/-!
# SubseqCompactOpen split — compact-open Vitali ball bridge wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact-open Vitali real-centre ball wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact-open Vitali ball bridges

## Compatibility re-export

The compact-open Vitali ball wrappers are split into
`CompactOpenVitali/Ball/Bridge.lean` and
`CompactOpenVitali/Ball/Real.lean`. This module preserves the old import path.
-/

/-!
# SubseqCompactOpen split — compact-open two-ball diagonal bridge

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact-open finite-ball diagonal bridge

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact-open finite diagonal bridges

Compatibility module re-exporting the compact-open finite diagonal child modules.
-/

/-!
# SubseqCompactOpen split — compact-open finite overlap bridge

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact-open Vitali bridges

Compatibility module re-exporting the compact-open Vitali child modules.
-/

end Ambient
end IsingModel
