import IsingModel.AmbientComplexAnalyticity.CompactOpen.VitaliFinBall

/-!
# Ambient compact-open extraction split — finite subsequence branch-limit families and patches

Part of the split ambient compact-open layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Packaged finite compact-open subsequence branch-limit family**: compact
open compactness on finitely many balls, plus eventual stage-level overlap
equality, produces a structured finite subsequence branch-limit family. This
packages the output of
`freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap`
for later coherent local-cover extraction steps. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
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
            Complex.exp ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    Nonempty (LeeYangFiniteSubseqBranchLimitFamily G Λ J β n h0 r) := by
  rcases freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨σ, hσ, f, hlocal, hcompat⟩
  exact ⟨{
    stage := σ
    stage_strict := hσ
    branchFamily := fun i m z => F i (σ m) z
    limitFun := f
    branch_spec := by
      intro i m
      rcases hbranch i (σ m) with ⟨han, hexp, _hcenter⟩
      exact ⟨han, hexp⟩
    centre_normalized := by
      intro i m
      exact (hbranch i (σ m)).2.2
    tendsto := by
      intro i
      exact (hlocal i).2.1
    differentiable := by
      intro i
      exact (hlocal i).2.2
    compatible := hcompat }⟩

/-- **Pointwise-normalised all-stage data to finite compact-open subsequence
package**: restrict pre-Montel all-stage branch choices to finitely many
Lee-Yang centres. Under compact-open compactness for the restricted branch
families and explicit eventual overlap equality, the existing finite
compact-open diagonal handoff produces a packaged finite subsequence
branch-limit family. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCompactOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β)
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
    Nonempty (LeeYangFiniteSubseqBranchLimitFamily G Λ J β n
      (fun i => (center i : ℂ))
      (fun i => data.branchData.radius (center i))) := by
  exact freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
    G Λ J β n
    (h0 := fun i => (center i : ℂ))
    (r := fun i => data.branchData.radius (center i))
    (F := fun i m z => data.branchData.branchFamily (center i) m z)
    hA hFc_mem hFres
    (by
      intro i m
      exact ⟨(data.branchData.branch_spec (center i) m).1,
        (data.branchData.branch_spec (center i) m).2,
        data.centre_normalized (center i) m⟩)
    hoverlap

/-- **Packaged finite subsequence branch-limit patching**: a compatible
`LeeYangFiniteSubseqBranchLimitFamily` patches to one function differentiable
on the finite union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : LeeYangFiniteSubseqBranchLimitFamily G Λ J β n h0 r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) := by
  rcases IsingModel.exists_differentiableOn_iUnion_of_finite_eqOn
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
      (f := family.limitFun)
      (hs := fun _ => Metric.isOpen_ball)
      (hdiff := family.differentiable)
      (hcompat := family.compatible) with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨g, hg_eq, hg_diff⟩

/-- **Packaged finite subsequence branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field
`p.h`, then a compatible `LeeYangFiniteSubseqBranchLimitFamily` patches on the
finite union of balls and the patched value at that real centre agrees with
`↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : LeeYangFiniteSubseqBranchLimitFamily G Λ (p.J : ℂ) (p.β : ℂ) n h0 r)
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
      G Λ (p.J : ℂ) (p.β : ℂ) n family with
    ⟨g, hg_eq, hg_diff⟩
  have hbranch : ∀ m,
      AnalyticOnNhd ℂ (family.branchFamily i₀ m)
          (Metric.ball (p.h : ℂ) (r i₀))
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) (r i₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume (family.stage m)) : Type _) : ℂ) *
                family.branchFamily i₀ m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (family.stage m))
        ∧ family.branchFamily i₀ m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (family.stage m) := by
    intro m
    rcases family.branch_spec i₀ m with ⟨han, hexp⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hcenter] using han
    · intro z hz
      exact hexp z (by simpa [hcenter] using hz)
    · simpa [hcenter] using family.centre_normalized i₀ m
  have hconv :
      TendstoLocallyUniformlyOn (family.branchFamily i₀) (family.limitFun i₀)
        Filter.atTop (Metric.ball (p.h : ℂ) (r i₀)) := by
    simpa [hcenter] using family.tendsto i₀
  have hidentified :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr family.stage_strict hbranch hconv
  have hcenter_mem :
      (p.h : ℂ) ∈ Metric.ball (h0 i₀) (r i₀) := by
    have hself : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) (r i₀) :=
      Metric.mem_ball_self hr
    simpa [hcenter] using hself
  have hg_center : g (p.h : ℂ) = family.limitFun i₀ (p.h : ℂ) :=
    hg_eq i₀ hcenter_mem
  exact ⟨g, hg_eq, hg_diff, hg_center.trans hidentified.2⟩


end Ambient
end IsingModel
