import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.FiniteSubseqCompactOpen

/-!
# Per-stage complex analyticity wrappers: FiniteCoverPatches

Consolidated `FiniteCoverPatches` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# SubseqCompactOpen split — finite Lee-Yang cover patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — finite real-centred Lee-Yang cover patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — compact finite real-centred cover patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — finite Lee-Yang cover patch wrappers

Compatibility module re-exporting the finite-cover patch child modules.
-/

/-!
# SubseqCompactOpen split — finite compact-open patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — pointwise all-stage finite compact-open patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/


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

/-!
# SubseqCompactOpen split — finite compact-open patch wrappers

## Compatibility re-export

The finite compact-open patch wrappers are split into
`FiniteCoverPatches/CompactOpen/FiniteFamily.lean` and
`FiniteCoverPatches/CompactOpen/Pointwise.lean`. This module preserves the old
import path.
-/

/-!
# SubseqCompactOpen split — finite Lee-Yang cover patching

Compatibility module re-exporting the finite-cover patch child modules.
-/

end Ambient
end IsingModel
