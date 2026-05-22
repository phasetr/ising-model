import IsingModel.AmbientComplexAnalyticity.BranchLocallyBoundedPatches

/-!
# Ambient complex analyticity compact cover patches

Mechanical child split from `AmbientComplexAnalyticity.lean`.
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

/-- **Compact local-cover `Fin n` geometry compact-open extraction to a
compact-target patch**: once a compact local-cover finite geometry has been
enumerated, compact-open compactness and eventual stage-level overlap equality
produce the compact finite real-centred Lee-Yang cover package and a patch
differentiable on the compact target. This is a one-input geometry wrapper
around `freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch`. -/
theorem freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ)
    (geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K)
    {F : Fin geometry.n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin geometry.n,
      Set C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    {Fc : ∀ i : Fin geometry.n, ℕ →
      C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))
        ∧ (∀ z ∈ Metric.ball
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (geometry.r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)
          ∩ Metric.ball
            ((geometry.center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r j))) :
    ∃ compactCover :
        LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
          geometry.n geometry.center geometry.r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch
    G Λ p hBED hd K geometry.n geometry.isCompact geometry.subset_domain
    geometry.real_mem geometry.cover_subset geometry.radius_pos geometry.ball_subset
    hA hFc_mem hFres hbranch hoverlap geometry.realIndex geometry.real_center

/-- **Structured eventual-overlap data to compact-open compact-target patch**:
structured real eventual-overlap data first yields a compact local-cover
`Fin n` geometry over `K`; for that geometry, compact-open compactness of the
selected restrictions of the data's branch family, together with centre
normalisation at every selected finite-cover centre, produces a compact finite
real-centred Lee-Yang cover package and a patch differentiable on `K`.

The extra selected-centre normalisation hypothesis is explicit because
`LeeYangRealEventualOverlapBranchData` only normalises the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealEventualOverlapBranchData G Λ p) :
    ∃ geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        (∀ i m,
          data.branchData.branchFamily (geometry.center i) m
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m) →
        ∃ compactCover :
            LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
              geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realFamily : LeeYangRealBranchLimitFamily G Λ p :=
    { centre_mem := data.centre_mem
      family :=
        { data := fun h₀ =>
            { radius := data.branchData.radius h₀
              radius_pos := data.branchData.radius_pos h₀
              ball_subset := data.branchData.ball_subset h₀
              branchFamily := data.branchData.branchFamily h₀
              limitFun := data.branchData.limitFun h₀
              branch_spec := data.branchData.branch_spec h₀
              tendsto := data.branchData.tendsto h₀ }
          compatible :=
            IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
              (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
                Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))
              (F := data.branchData.branchFamily) (f := data.branchData.limitFun)
              data.branchData.tendsto data.branchData.overlap_eventually }
      centre_normalized := data.centre_normalized }
  classical
  rcases exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
      G Λ p hK hKsub hpK realFamily with
    ⟨t, ht_real, ht_cover⟩
  let center : Fin t.card → {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    fun i => ((t.equivFin).symm i).1
  let r : Fin t.card → ℝ :=
    fun i => data.branchData.radius (center i)
  let realIndex : Fin t.card := t.equivFin ⟨⟨(p.h : ℂ), realFamily.centre_mem⟩, ht_real⟩
  let geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K :=
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      realFamily := realFamily
      n := t.card
      center := center
      r := r
      radius_eq := by
        intro i
        rfl
      radius_pos := by
        intro i
        exact data.branchData.radius_pos (center i)
      ball_subset := by
        intro i
        exact data.branchData.ball_subset (center i)
      cover_subset := by
        intro z hzK
        rcases Set.mem_iUnion.mp (ht_cover hzK) with ⟨h₀, hz⟩
        rcases Set.mem_iUnion.mp hz with ⟨h₀_mem, hz_ball⟩
        let h₀' : t := ⟨h₀, h₀_mem⟩
        let i : Fin t.card := t.equivFin h₀'
        have hcenter : center i = h₀ := by
          simp [center, i, h₀']
        exact Set.mem_iUnion.mpr
          ⟨i, by
            dsimp [r]
            rw [hcenter]
            exact hz_ball⟩
      realIndex := realIndex
      real_center := by
        simp [center, realIndex] }
  refine ⟨geometry, ?_⟩
  intro A Fc hA hFc_mem hFres hcenter_normalized
  let F : Fin geometry.n → ℕ → ℂ → ℂ :=
    fun i => data.branchData.branchFamily (geometry.center i)
  have hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))
        ∧ (∀ z ∈ Metric.ball
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (geometry.r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m := by
    intro i m
    rcases data.branchData.branch_spec (geometry.center i) m with ⟨han, hexp⟩
    have hradius : geometry.r i = data.branchData.radius (geometry.center i) := by
      simpa [realFamily] using geometry.radius_eq i
    refine ⟨?_, ?_, hcenter_normalized i m⟩
    · simpa [F, hradius] using han
    · simpa [F, hradius] using hexp
  have hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)
          ∩ Metric.ball
            ((geometry.center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r j)) := by
    intro i j
    have hradius_i : geometry.r i = data.branchData.radius (geometry.center i) := by
      simpa [realFamily] using geometry.radius_eq i
    have hradius_j : geometry.r j = data.branchData.radius (geometry.center j) := by
      simpa [realFamily] using geometry.radius_eq j
    simpa [F, hradius_i, hradius_j] using
      data.branchData.overlap_eventually (geometry.center i) (geometry.center j)
  exact freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch
    G Λ p hBED hd K geometry hA hFc_mem hFres hbranch hoverlap

/-- **Pointwise-normalised eventual-overlap data to compact-open compact-target
patch**: the pointwise-normalised package supplies the selected-centre
normalisation required by
`freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch`.
Thus only compact-open compactness of the selected branch-family restrictions
and their continuous representatives remain as explicit compact-open inputs. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    ∃ geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.pointwiseData.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        ∃ compactCover :
            LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
              geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realData : LeeYangRealEventualOverlapBranchData G Λ p :=
    LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised G Λ p data
  rcases freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch
      G Λ p hBED hd hK hKsub hpK realData with
    ⟨geometry, hgeometry⟩
  refine ⟨geometry, ?_⟩
  intro A Fc hA hFc_mem hFres
  refine hgeometry hA hFc_mem hFres ?_
  intro i m
  exact data.pointwiseData.centre_normalized (geometry.center i) m

/-- **Finite-ball compact-open diagonal extraction with local patching**:
if the finite Lee-Yang local limits obtained from compact-open extraction are
compatible on all pairwise ball overlaps, then they patch to one function on
the finite union of balls.  The stage-level overlap equality remains an
explicit hypothesis, inherited from
`freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_patch
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
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ, ∃ g : ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        (∀ i, Set.EqOn g (f i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) := by
  rcases freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨σ, hσ, f, hlocal, hcompat⟩
  rcases IsingModel.exists_differentiableOn_iUnion_of_finite_eqOn
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i)) (f := f)
      (hs := fun _ => Metric.isOpen_ball)
      (hdiff := fun i => (hlocal i).2.2)
      (hcompat := hcompat) with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨σ, hσ, f, g, hlocal, hg_eq, hg_diff, hcompat⟩

end Ambient

end IsingModel
