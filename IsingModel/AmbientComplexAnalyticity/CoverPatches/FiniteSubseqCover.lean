import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches

/-!
# Cover patches split — finite subsequence and finite cover compact-open patches

Part of the split cover-patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Finite compact-open extraction to a real-centre patch**: compact-open
compactness on finitely many balls, eventual stage-level overlap equality, and
a selected ball centred at the real field `p.h` produce a patched function on
the finite union of balls whose value at `p.h` is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
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
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (h0 i) (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)))
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ family : LeeYangFiniteSubseqBranchLimitFamily G Λ
        (p.J : ℂ) (p.β : ℂ) n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hA hFc_mem hFres hbranch hoverlap with
    ⟨family⟩
  exact ⟨family,
    freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
      G Λ p hBED hd n family i₀ hcenter hr⟩

/-- **Finite Lee-Yang cover compact-open extraction package**: compact-open
compactness on finitely many Lee-Yang-domain balls, plus eventual stage-level
overlap equality, produces a finite Lee-Yang cover branch-limit family. The
balls are recorded with their positivity and containment in `leeYangDomain`
for later local-cover diagonalization. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
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
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    Nonempty (LeeYangFiniteCoverBranchLimitFamily G Λ J β n center r) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨family⟩
  exact ⟨{
    radius_pos := hr
    ball_subset := hsub
    family := family }⟩

/-- **Finite Lee-Yang cover compact-open extraction to a patch**:
compact-open compactness and eventual stage-level overlap equality produce
both the finite Lee-Yang cover package and a differentiable patch on the finite
union of its Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
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
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    ∃ cover : LeeYangFiniteCoverBranchLimitFamily G Λ J β n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ J β n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  exact ⟨cover,
    freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
      G Λ J β n cover⟩


end Ambient
end IsingModel
