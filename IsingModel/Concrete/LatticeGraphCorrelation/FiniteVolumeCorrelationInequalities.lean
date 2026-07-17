import IsingModel.Inequalities.GHS
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume correlation inequality wrappers

Narrow child module for concrete `latticeGraph` finite-volume correlation and
truncated-correlation inequality, symmetry, and trivial-slice wrappers. The
theorem names are the same as the former declarations, but callers can
now avoid importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume correlation and truncated-correlation inequalities -/

/-- **ℤ^d Cor 4.3.5 at `h = 0`, Λ-induced subgraph** (GJ §4.3 Cor 4.3.5):
inductive `(n+2)`-point bound at finite volume. -/
theorem cor_4_3_5_h0_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hf : Ferromagnetic (⟨J, (0 : ℝ), β⟩ : IsingParams ℝ))
    (S : Finset (↑Λ)) (j k : ↑Λ) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    IsingModel.correlation (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) (insert j (insert k S))
      ≤ IsingModel.correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (⟨J, 0, β⟩ : IsingParams ℝ) S
          * IsingModel.correlation
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, 0, β⟩ : IsingParams ℝ) {j, k}
        + ∑ T ∈ S.powerset,
            IsingModel.correlation
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                (⟨J, 0, β⟩ : IsingParams ℝ) (insert j T)
              * IsingModel.correlation
                  (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) (insert k (S \ T)) :=
  IsingModel.cor_4_3_5_h0
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hf S j k hj hk hjk

/-- **ℤ^d correlation_odd_vanish** at Λ-induced: at `h = 0`, the
correlation `⟨σ^A⟩ = 0` for any odd-cardinality `A`. -/
theorem correlation_odd_vanish_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (↑Λ : Type _)) (hodd : Odd A.card) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_odd_vanish
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β A hodd

/-! ## Moved: truncated{2,3} finite-volume trivial-slice wrappers

The four wrappers
`truncated2_J_zero_of_ne_latticeGraph`,
`truncated2_beta_zero_latticeGraph`,
`truncated3_J_zero_of_pairwise_distinct_latticeGraph`,
`truncated3_beta_zero_latticeGraph` now live in
`FiniteVolumeCorrelationInequalitiesTrivialSlice.lean`. -/


/-- **ℤ^d truncated2 nonneg** at Λ-induced (ferromagnetic). -/
theorem truncated2_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : ↑Λ) :
    0 ≤ IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.truncated2_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j

/-- **ℤ^d GHS inequality at Λ-induced subgraph** (Glimm–Jaffe §4.3 Cor 4.3.4):
`U_3(i, j, k) ≤ 0` for ferromagnetic `p` and distinct sites. -/
theorem ghs_inequality_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j k : ↑Λ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j k ≤ 0 :=
  IsingModel.ghs_inequality
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j k hij hjk hik

/-! ## Moved: truncated-four-point wrappers

The three `truncated4_beta_zero_latticeGraph`,
`truncated4_J_zero_of_pairwise_distinct_latticeGraph`, and
`cor_4_3_3_latticeGraph` wrappers now live in
`FiniteVolumeCorrelationInequalitiesTruncated4.lean`. -/



end Ambient
end IsingModel
