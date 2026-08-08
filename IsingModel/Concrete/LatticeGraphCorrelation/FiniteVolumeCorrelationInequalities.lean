import IsingModel.Inequalities.GHS
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Correlation and truncated-correlation inequalities at finite volume in ℤ^d

Records, on the subgraph induced by the nearest-neighbor lattice graph on a finite
`Λ ⊆ ℤ^d`, the zero-field bound of the correlation over `S ∪ {j, k}` by the correlation
over `S` times the pair correlation of `j` and `k`, plus a sum over the splittings of `S`;
the vanishing of odd-cardinality correlations at zero external field; nonnegativity of the
truncated two-point function; and nonpositivity of the truncated three-point function at
pairwise distinct sites.

The zero-field statements put `0` in the field slot of the parameter record. The
odd-vanishing one adds only that `A` has odd cardinality, imposing no condition on the
coupling or the inverse temperature; the `S ∪ {j, k}` bound also assumes the ferromagnetic
condition and that `j` and `k` are distinct and lie outside `S`. The truncated statements
assume the ferromagnetic condition at an otherwise arbitrary parameter record, and the
two-point one is stated at sites that need not be distinct.

Reference: Glimm–Jaffe §4.3, Corollary 4.3.5, p. 63, for the `S ∪ {j, k}` bound, which is
the inductive step of its proof, and Corollary 4.3.4, p. 62, for the GHS inequality.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
