import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d tail GKS / FKG / supermodular wrappers

Narrow child module for four ℤ^d Λ-induced ferromagnetic correlation
wrappers extracted from `MagnetizationGksFkg.lean`:

* `gks_first_latticeGraph` (GKS-I),
* `gks_second_latticeGraph` (GKS-II),
* `boltzmannWeight_log_supermodular_latticeGraph`,
* `fkg_ising_latticeGraph` (FKG).
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d GKS-I at Λ-induced subgraph** (Griffiths 1967):
`0 ≤ ⟨σ^A⟩_Λ` for ferromagnetic `p`. -/
theorem gks_first_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ)) :
    0 ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  IsingModel.gks_first
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A

/-- **ℤ^d GKS-II at Λ-induced subgraph** (Griffiths 1967):
`⟨σ^A⟩_Λ · ⟨σ^B⟩_Λ ≤ ⟨σ^{A Δ B}⟩_Λ` for ferromagnetic `p`. -/
theorem gks_second_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (↑Λ)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A
      * IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p B
      ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (symmDiff A B) :=
  IsingModel.gks_second
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A B

/-- **ℤ^d boltzmannWeight log-supermodularity** (Λ-induced,
ferromagnetic): `w(σ) · w(σ') ≤ w(σ ⊔ σ') · w(σ ⊓ σ')`. Thin
pass-through of `IsingModel.boltzmannWeight_log_supermodular`; the
technical input to `fkg_ising`. -/
theorem boltzmannWeight_log_supermodular_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (σ σ' : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.boltzmannWeight
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ
      * IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ'
      ≤ IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (σ ⊔ σ')
        * IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (σ ⊓ σ') :=
  IsingModel.boltzmannWeight_log_supermodular
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf σ σ'

/-- **ℤ^d FKG inequality** (Λ-induced, ferromagnetic, GJ §4.4): for
nonneg monotone `f, g : Config (↑Λ) → ℝ`,
`⟨f⟩ · ⟨g⟩ ≤ ⟨f · g⟩`. Thin pass-through of
`IsingModel.fkg_ising`. -/
theorem fkg_ising_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (f g : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hf_nn : 0 ≤ f) (hg_nn : 0 ≤ g)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    IsingModel.gibbsExpectation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p f
      * IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p g
      ≤ IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (f * g) :=
  IsingModel.fkg_ising
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf
    f g hf_nn hg_nn hf_mono hg_mono

end Ambient
end IsingModel
