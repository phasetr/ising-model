import IsingModel.InfiniteVolume
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Gibbs expectations and the coupling slice of the correlation at finite volume in ℤ^d

Records, on the subgraph induced by the nearest-neighbor lattice graph on a finite
`Λ ⊆ ℤ^d`, the covariance inequality behind the reweighting arguments: the unnormalized
covariance of a spin product against a function with nonnegative correlations is
nonnegative at a ferromagnetic parameter record. It also records the Gibbs expectation as
the inverse partition function times the unnormalized expectation, the transfer of
nonnegativity from that unnormalized expectation to the Gibbs expectation, and the range of
the correlation read as a function of the coupling: nonnegative by the first Griffiths
inequality under `0 ≤ J`, `0 ≤ h` and `0 < β`, and at most `1` with no condition on the
parameters at all. The nonnegative-correlations condition belongs to the covariance
inequality alone, which is also the only statement here that takes the ferromagnetic
condition as a bundled hypothesis; the coupling nonnegativity assumes the same sign
conditions separately. The ratio presentation holds at an arbitrary parameter record, and
the nonnegativity transfer holds there under its numerator hypothesis.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d cov_hnc_boltzmann_nonneg direct** (Λ-induced, ferromagnetic):
covariance bound for HNC `f` with Boltzmann weight. -/
theorem cov_hnc_boltzmann_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hferm : Ferromagnetic p)
    (f : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hf : IsingModel.HasNonnegCorrelations f) (B : Finset (↑Λ : Type _)) :
    0 ≤ (∑ σ, IsingModel.spinProduct B σ * f σ
            * IsingModel.boltzmannWeight
                (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) -
      (∑ σ, IsingModel.spinProduct B σ *
          IsingModel.boltzmannWeight
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) *
        (∑ σ, f σ * IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ) :=
  IsingModel.cov_hnc_boltzmann_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hferm f hf B

/-- **ℤ^d gibbsExpectation as ratio** at Λ-induced:
`⟨F⟩ = Z⁻¹ · numerator(F)`. -/
theorem gibbsExpectation_eq_div_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ) :
    IsingModel.gibbsExpectation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F
      = (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p)⁻¹
          * IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_eq_div
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F

/-- **ℤ^d gibbsExpectation nonneg from numerator nonneg** at Λ-induced. -/
theorem gibbsExpectation_nonneg_of_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (F : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hnum : 0 ≤ IsingModel.numerator
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F) :
    0 ≤ IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F :=
  IsingModel.gibbsExpectation_nonneg_of_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p F hnum

/-- **ℤ^d correlationJ_nonneg direct** (Λ-induced, ferromagnetic): for
`h ≥ 0`, `β > 0`, and `J ≥ 0`, `0 ≤ correlationJ (inducedGraph … Λ) h β B J`.
Thin pass-through of `IsingModel.correlationJ_nonneg`; GJ §4.2 Prop 4.2.1
slice at `correlationJ` (GKS-I). -/
theorem correlationJ_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (B : Finset (↑Λ : Type _)) (J : ℝ) (hJ : 0 ≤ J) :
    0 ≤ IsingModel.correlationJ
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J :=
  IsingModel.correlationJ_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ B J hJ

/-- **ℤ^d correlationJ_le_one direct** (Λ-induced): for every `J`,
`correlationJ (inducedGraph … Λ) h β B J ≤ 1`. Thin pass-through of
`IsingModel.correlationJ_le_one` (unconditional upper bound). -/
theorem correlationJ_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (B : Finset (↑Λ : Type _)) (J : ℝ) :
    IsingModel.correlationJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J ≤ 1 :=
  IsingModel.correlationJ_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β B J

end Ambient
end IsingModel
