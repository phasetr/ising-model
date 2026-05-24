import IsingModel.AmbientComplexAnalyticity.CoverPatches.FiniteSubseqCover

/-!
# Cover patches split — real-cover and compact finite real-cover compact-open patches

Part of the split cover-patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Finite Lee-Yang cover compact-open extraction to a real-centre patch**:
compact-open compactness and eventual stage-level overlap equality produce a
finite Lee-Yang cover package and a finite-union patch whose selected real
centre value is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ cover : LeeYangFiniteCoverBranchLimitFamily
        G Λ (p.J : ℂ) (p.β : ℂ) n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  exact ⟨cover,
    freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
      G Λ p hBED hd n cover i₀ hcenter⟩

/-- **Finite Lee-Yang cover compact-open extraction to a real-centred package
and patch**: compact-open compactness and eventual stage-level overlap equality
produce a finite real-centred Lee-Yang cover package and a finite-union patch
whose selected real-centre value is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  let realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r :=
    { cover := cover
      realIndex := i₀
      real_center := hcenter }
  exact ⟨realCover,
    freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
      G Λ p hBED hd n realCover⟩

/-- **Compact finite Lee-Yang cover compact-open extraction to a real-centred
package and compact-target patch**: compact-open compactness and eventual
stage-level overlap equality produce a compact finite real-centred Lee-Yang
cover package and a patch differentiable on the compact target. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover :
        LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch
      G Λ p hBED hd n hr hsub hA hFc_mem hFres hbranch hoverlap i₀ hcenter with
    ⟨realCover, g, hg_eq, hg_diff, hg_real⟩
  let compactCover :
      LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center r :=
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      cover_subset := hKcover
      realCover := realCover }
  exact ⟨compactCover, g, hg_eq, hg_diff.mono hKcover, hg_real⟩


end Ambient
end IsingModel
