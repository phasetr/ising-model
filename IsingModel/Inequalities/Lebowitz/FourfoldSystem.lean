import IsingModel.Inequalities.Lebowitz.FourfoldSite

/-!
# The fourfold duplicate Ising system (GJ §4.3)

Four independent copies of the Ising system on one graph: the product weight, the partition
function `Z⁴`, the product expectation, the factorisation of expectations of products of
per-copy observables, and the site-indexed Hadamard variables with their `Finset` products —
the system-level objects of GJ Theorem 4.3.1.

* `QuadConfig`, `quadWeight`, `quadPartition`, `quadExpectation` — the fourfold system.
* `quadPartition_eq` — `Z₄ = Z⁴`.
* `quadExpectation_factor` — `⟨F(ξ)G(χ)H(ξ')K(χ')⟩₄ = ⟨F⟩⟨G⟩⟨H⟩⟨K⟩`.
* `uSite` / `uProd` — the site-indexed Hadamard variables and their `Finset` products.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Theorem 4.3.1, pp. 59–61.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The fourfold configuration space: four independent copies `(ξ, χ, ξ', χ')` of the spin
configuration space. -/
abbrev QuadConfig (ι : Type*) : Type _ := Config ι × Config ι × Config ι × Config ι

/-- The fourfold product Boltzmann weight `w(ξ)w(χ)w(ξ')w(χ')`. -/
noncomputable def quadWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (v : QuadConfig ι) : ℝ :=
  boltzmannWeight G p v.1 * boltzmannWeight G p v.2.1 *
    boltzmannWeight G p v.2.2.1 * boltzmannWeight G p v.2.2.2

/-- The fourfold partition function. -/
noncomputable def quadPartition (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  ∑ v : QuadConfig ι, quadWeight G p v

omit [DecidableEq ι] in
/-- The fourfold weight is positive. -/
theorem quadWeight_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (v : QuadConfig ι) : 0 < quadWeight G p v :=
  mul_pos (mul_pos (mul_pos (boltzmannWeight_pos G p v.1)
    (boltzmannWeight_pos G p v.2.1)) (boltzmannWeight_pos G p v.2.2.1))
    (boltzmannWeight_pos G p v.2.2.2)

/-- **The fourfold partition function factorises**: `Z₄ = Z⁴`. -/
theorem quadPartition_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    quadPartition G p = partitionFunction G p ^ 4 := by
  unfold quadPartition quadWeight partitionFunction
  simp only [Fintype.sum_prod_type]
  have h4 : ∀ σ τ ρ : Config ι,
      ∑ κ : Config ι, boltzmannWeight G p σ * boltzmannWeight G p τ *
        boltzmannWeight G p ρ * boltzmannWeight G p κ
      = boltzmannWeight G p σ * boltzmannWeight G p τ * boltzmannWeight G p ρ *
        ∑ κ : Config ι, boltzmannWeight G p κ := by
    intro σ τ ρ
    rw [← Finset.mul_sum]
  simp_rw [h4]
  have h3 : ∀ σ τ : Config ι,
      ∑ ρ : Config ι, boltzmannWeight G p σ * boltzmannWeight G p τ *
        boltzmannWeight G p ρ * ∑ κ : Config ι, boltzmannWeight G p κ
      = boltzmannWeight G p σ * boltzmannWeight G p τ *
        (∑ ρ : Config ι, boltzmannWeight G p ρ) *
        ∑ κ : Config ι, boltzmannWeight G p κ := by
    intro σ τ
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h3]
  have h2 : ∀ σ : Config ι,
      ∑ τ : Config ι, boltzmannWeight G p σ * boltzmannWeight G p τ *
        (∑ ρ : Config ι, boltzmannWeight G p ρ) *
        ∑ κ : Config ι, boltzmannWeight G p κ
      = boltzmannWeight G p σ * (∑ τ : Config ι, boltzmannWeight G p τ) *
        (∑ ρ : Config ι, boltzmannWeight G p ρ) *
        ∑ κ : Config ι, boltzmannWeight G p κ := by
    intro σ
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [h2]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The fourfold partition function is positive. -/
theorem quadPartition_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : 0 < quadPartition G p := by
  rw [quadPartition_eq]
  exact pow_pos (partitionFunction_pos G p) 4

/-- The fourfold Gibbs expectation. -/
noncomputable def quadExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : QuadConfig ι → ℝ) : ℝ :=
  (quadPartition G p)⁻¹ * ∑ v : QuadConfig ι, F v * quadWeight G p v

/-- **Factorisation of fourfold expectations of per-copy products**:
`⟨F(ξ)G(χ)H(ξ')K(χ')⟩₄ = ⟨F⟩⟨G⟩⟨H⟩⟨K⟩`. -/
theorem quadExpectation_factor (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F₁ F₂ F₃ F₄ : Config ι → ℝ) :
    quadExpectation G p (fun v => F₁ v.1 * F₂ v.2.1 * F₃ v.2.2.1 * F₄ v.2.2.2)
      = gibbsExpectation G p F₁ * gibbsExpectation G p F₂ *
        gibbsExpectation G p F₃ * gibbsExpectation G p F₄ := by
  unfold quadExpectation gibbsExpectation
  rw [quadPartition_eq]
  have hZ := partitionFunction_ne_zero G p
  have hsum : ∑ v : QuadConfig ι,
      (F₁ v.1 * F₂ v.2.1 * F₃ v.2.2.1 * F₄ v.2.2.2) * quadWeight G p v
      = (∑ σ, F₁ σ * boltzmannWeight G p σ) * (∑ σ, F₂ σ * boltzmannWeight G p σ) *
        (∑ σ, F₃ σ * boltzmannWeight G p σ) * (∑ σ, F₄ σ * boltzmannWeight G p σ) := by
    unfold quadWeight
    simp only [Fintype.sum_prod_type]
    have h4 : ∀ σ τ ρ : Config ι,
        ∑ κ : Config ι, (F₁ σ * F₂ τ * F₃ ρ * F₄ κ) *
          (boltzmannWeight G p σ * boltzmannWeight G p τ *
            boltzmannWeight G p ρ * boltzmannWeight G p κ)
        = (F₁ σ * boltzmannWeight G p σ) * (F₂ τ * boltzmannWeight G p τ) *
          (F₃ ρ * boltzmannWeight G p ρ) *
          ∑ κ : Config ι, F₄ κ * boltzmannWeight G p κ := by
      intro σ τ ρ
      have hgr : ∀ κ : Config ι,
          (F₁ σ * F₂ τ * F₃ ρ * F₄ κ) *
            (boltzmannWeight G p σ * boltzmannWeight G p τ *
              boltzmannWeight G p ρ * boltzmannWeight G p κ)
          = (F₁ σ * boltzmannWeight G p σ) * (F₂ τ * boltzmannWeight G p τ) *
            (F₃ ρ * boltzmannWeight G p ρ) * (F₄ κ * boltzmannWeight G p κ) :=
        fun κ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h4]
    have h3 : ∀ σ τ : Config ι,
        ∑ ρ : Config ι, (F₁ σ * boltzmannWeight G p σ) *
          (F₂ τ * boltzmannWeight G p τ) * (F₃ ρ * boltzmannWeight G p ρ) *
          ∑ κ : Config ι, F₄ κ * boltzmannWeight G p κ
        = (F₁ σ * boltzmannWeight G p σ) * (F₂ τ * boltzmannWeight G p τ) *
          (∑ ρ : Config ι, F₃ ρ * boltzmannWeight G p ρ) *
          ∑ κ : Config ι, F₄ κ * boltzmannWeight G p κ := by
      intro σ τ
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    simp_rw [h3]
    have h2 : ∀ σ : Config ι,
        ∑ τ : Config ι, (F₁ σ * boltzmannWeight G p σ) *
          (F₂ τ * boltzmannWeight G p τ) *
          (∑ ρ : Config ι, F₃ ρ * boltzmannWeight G p ρ) *
          ∑ κ : Config ι, F₄ κ * boltzmannWeight G p κ
        = (F₁ σ * boltzmannWeight G p σ) *
          (∑ τ : Config ι, F₂ τ * boltzmannWeight G p τ) *
          (∑ ρ : Config ι, F₃ ρ * boltzmannWeight G p ρ) *
          ∑ κ : Config ι, F₄ κ * boltzmannWeight G p κ := by
      intro σ
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    simp_rw [h2]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [hsum]
  field_simp

/-- The four spins of the fourfold configuration at one site, as a single-site quadruple. -/
def siteQuadAt (v : QuadConfig ι) (i : ι) : SiteQuad :=
  (v.1 i, v.2.1 i, v.2.2.1 i, v.2.2.2 i)

/-- The site-indexed first Hadamard variable `u₁(i) = ξᵢ + χᵢ + ξ'ᵢ + χ'ᵢ`. -/
noncomputable def uSite₁ (i : ι) (v : QuadConfig ι) : ℝ := u₁ (siteQuadAt v i)
/-- The site-indexed second Hadamard variable `u₂(i) = ξᵢ + χᵢ − ξ'ᵢ − χ'ᵢ`. -/
noncomputable def uSite₂ (i : ι) (v : QuadConfig ι) : ℝ := u₂ (siteQuadAt v i)
/-- The site-indexed third Hadamard variable `u₃(i) = ξᵢ − χᵢ + ξ'ᵢ − χ'ᵢ`. -/
noncomputable def uSite₃ (i : ι) (v : QuadConfig ι) : ℝ := u₃ (siteQuadAt v i)
/-- The site-indexed fourth Hadamard variable `u₄(i) = −ξᵢ + χᵢ + ξ'ᵢ − χ'ᵢ` (even-subgroup
sign convention, cf. `FourfoldSite`). -/
noncomputable def uSite₄ (i : ι) (v : QuadConfig ι) : ℝ := u₄ (siteQuadAt v i)

/-- The `Finset` product of first Hadamard variables, `u₁^A := ∏_{i ∈ A} u₁(i)` (the
fourfold analogue of `spinProduct`). -/
noncomputable def uProd₁ (A : Finset ι) (v : QuadConfig ι) : ℝ := ∏ i ∈ A, uSite₁ i v
/-- The `Finset` product of second Hadamard variables. -/
noncomputable def uProd₂ (A : Finset ι) (v : QuadConfig ι) : ℝ := ∏ i ∈ A, uSite₂ i v
/-- The `Finset` product of third Hadamard variables. -/
noncomputable def uProd₃ (A : Finset ι) (v : QuadConfig ι) : ℝ := ∏ i ∈ A, uSite₃ i v
/-- The `Finset` product of fourth Hadamard variables. -/
noncomputable def uProd₄ (A : Finset ι) (v : QuadConfig ι) : ℝ := ∏ i ∈ A, uSite₄ i v

end Lebowitz

end IsingModel
