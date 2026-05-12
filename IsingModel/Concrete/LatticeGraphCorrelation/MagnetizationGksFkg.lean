import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.Concrete.LatticeGraphCorrelation.Magnetization

/-!
# ℤ^d HNC / GKS / FKG wrappers on `latticeGraph d`

Narrow child module for 12 `hasNonnegCorrelations_*_latticeGraph` /
`gks_*_latticeGraph` / `boltzmannWeight_*_latticeGraph` /
`fkg_ising_latticeGraph` thin pass-throughs of the abstract HNC /
GKS / FKG bridges on the induced subgraph
`inducedGraph (latticeGraph d) Λ`. Theorem names are unchanged from
the former `Magnetization` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d hasNonnegCorrelations_one direct** (Λ-induced):
the constant function `1` has HNC. -/
theorem hasNonnegCorrelations_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsingModel.HasNonnegCorrelations
      (ι := (↑Λ : Type _)) (fun _ => 1) :=
  IsingModel.hasNonnegCorrelations_one

/-- **ℤ^d hasNonnegCorrelations_finset_prod direct** (Λ-induced):
a product of `(a + b · σ^C)` factors over a Finset has HNC. -/
theorem hasNonnegCorrelations_finset_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_finset_prod S g hg

/-- **ℤ^d hasNonnegCorrelations_mul_prod direct** (Λ-induced):
multiplying an HNC function by a product of `(a + b · σ^C)` factors
preserves HNC. -/
theorem hasNonnegCorrelations_mul_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α) {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_mul_prod S hf g hg

/-- **ℤ^d hasNonnegCorrelations_mul direct** (Λ-induced): if `f` has HNC
then so does `f · (a + b · σ^C)` for `a, b ≥ 0`. -/
theorem hasNonnegCorrelations_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (C : Finset (↑Λ : Type _)) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * (a + b * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_mul hf ha hb C

/-- **ℤ^d hasNonnegCorrelations_general_coupling direct** (Λ-induced):
general non-negative couplings give HNC product. -/
theorem hasNonnegCorrelations_general_coupling_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (couplings : Finset (Finset (↑Λ : Type _)))
    (K : Finset (↑Λ : Type _) → ℝ)
    (hK : ∀ C ∈ couplings, 0 ≤ K C) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ C ∈ couplings, Real.exp (K C * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_general_coupling couplings K hK

/-- **ℤ^d hasNonnegCorrelations_edge_site_product direct** (Λ-induced):
the edge × site product weight has HNC on `Config ↑Λ`. -/
theorem hasNonnegCorrelations_edge_site_product_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (edgeK : Sym2 (↑Λ : Type _) → ℝ) (siteK : (↑Λ : Type _) → ℝ)
    (hedgeK : ∀ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
      0 ≤ edgeK e)
    (hsiteK : ∀ i, 0 ≤ siteK i) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      (∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Real.exp (edgeK e * IsingModel.edgeSpin (K := ℝ) σ e)) *
      (∏ i : (↑Λ : Type _),
        Real.exp (siteK i * IsingModel.Spin.sign ℝ (σ i))) :=
  IsingModel.hasNonnegCorrelations_edge_site_product
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) edgeK siteK hedgeK hsiteK

/-- **ℤ^d GKS numerator nonneg** at Λ-induced: for ferromagnetic `p`,
`0 ≤ numerator (spinProduct A)`. -/
theorem gks_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    0 ≤ IsingModel.numerator
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
          (IsingModel.spinProduct A) :=
  IsingModel.gks_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A

/-- **ℤ^d boltzmannWeight has non-negative correlations** at Λ-induced
(ferromagnetic). -/
theorem boltzmannWeight_hasNonnegCorrelations_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.HasNonnegCorrelations (IsingModel.boltzmannWeight
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.boltzmannWeight_hasNonnegCorrelations
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

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
