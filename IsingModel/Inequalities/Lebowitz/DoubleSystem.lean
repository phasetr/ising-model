import IsingModel.Inequalities.Lebowitz.Theorem431

/-!
# The doubled Ising system and the t/q variables (GJ §4.3)

Two independent copies of the Ising system, the `t`/`q` rotated variables (unnormalised:
`t = ξ + χ`, `q = ξ − χ` at the spin-sign level; GJ's `√2` normalisation only contributes
positive scalars to the inequalities), and the bridges to the fourfold system of
Theorem 4.3.1: the pair factorisation `⟨F(ξ,χ)G(ξ',χ')⟩₄ = ⟨F⟩₂⟨G⟩₂` and the inverse
rotation `t = (u₁+u₂)/2`, `t' = (u₁−u₂)/2`, `q = (u₃−u₄)/2`, `q' = (u₃+u₄)/2` (matching the
even-subgroup `u₄` orientation).

* `DoubleConfig`, `doubleWeight`, `doublePartition`, `doubleExpectation` — the doubled system.
* `doubleExpectation_factor` — `⟨F(ξ)G(χ)⟩₂ = ⟨F⟩⟨G⟩`.
* `quadExpectation_factor_pair` / `quadExpectation_fst_pair` — the 2+2 factorisation.
* `tSite` / `qSite` / `tProd` / `qProd` — the rotated variables and their `Finset` products.
* `tSite_fst_eq` etc. — the inverse-rotation identities against the Hadamard variables.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.3,
Corollary 4.3.2, p. 60.
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The doubled configuration space: two independent copies `(ξ, χ)`. -/
abbrev DoubleConfig (ι : Type*) : Type _ := Config ι × Config ι

/-- The doubled product Boltzmann weight `w(ξ)w(χ)`. -/
noncomputable def doubleWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (d : DoubleConfig ι) : ℝ :=
  boltzmannWeight G p d.1 * boltzmannWeight G p d.2

/-- The doubled partition function. -/
noncomputable def doublePartition (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  ∑ d : DoubleConfig ι, doubleWeight G p d

/-- **The doubled partition function factorises**: `Z₂ = Z²`. -/
theorem doublePartition_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    doublePartition G p = partitionFunction G p ^ 2 := by
  unfold doublePartition doubleWeight partitionFunction
  rw [Fintype.sum_prod_type]
  have h1 : ∀ σ : Config ι,
      ∑ τ : Config ι, boltzmannWeight G p σ * boltzmannWeight G p τ
        = boltzmannWeight G p σ * ∑ τ : Config ι, boltzmannWeight G p τ := by
    intro σ
    rw [← Finset.mul_sum]
  simp_rw [h1]
  rw [← Finset.sum_mul]
  ring

/-- The doubled partition function is positive. -/
theorem doublePartition_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : 0 < doublePartition G p := by
  rw [doublePartition_eq]
  exact pow_pos (partitionFunction_pos G p) 2

/-- The doubled Gibbs expectation. -/
noncomputable def doubleExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : DoubleConfig ι → ℝ) : ℝ :=
  (doublePartition G p)⁻¹ * ∑ d : DoubleConfig ι, F d * doubleWeight G p d

/-- **Factorisation of doubled expectations of per-copy products**:
`⟨F(ξ)G(χ)⟩₂ = ⟨F⟩⟨G⟩`. -/
theorem doubleExpectation_factor (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F₁ F₂ : Config ι → ℝ) :
    doubleExpectation G p (fun d => F₁ d.1 * F₂ d.2)
      = gibbsExpectation G p F₁ * gibbsExpectation G p F₂ := by
  unfold doubleExpectation gibbsExpectation
  rw [doublePartition_eq]
  have hZ := partitionFunction_ne_zero G p
  have hsum : ∑ d : DoubleConfig ι, (F₁ d.1 * F₂ d.2) * doubleWeight G p d
      = (∑ σ, F₁ σ * boltzmannWeight G p σ) * ∑ σ, F₂ σ * boltzmannWeight G p σ := by
    unfold doubleWeight
    rw [Fintype.sum_prod_type]
    have h1 : ∀ σ : Config ι,
        ∑ τ : Config ι, (F₁ σ * F₂ τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)
          = (F₁ σ * boltzmannWeight G p σ) *
            ∑ τ : Config ι, F₂ τ * boltzmannWeight G p τ := by
      intro σ
      have hgr : ∀ τ : Config ι,
          (F₁ σ * F₂ τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)
            = (F₁ σ * boltzmannWeight G p σ) * (F₂ τ * boltzmannWeight G p τ) :=
        fun τ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h1]
    rw [← Finset.sum_mul]
  rw [hsum]
  field_simp

/-- **Pair factorisation of the fourfold expectation**:
`⟨F(ξ,χ)G(ξ',χ')⟩₄ = ⟨F⟩₂⟨G⟩₂`. -/
theorem quadExpectation_factor_pair (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F₁ F₂ : DoubleConfig ι → ℝ) :
    quadExpectation G p (fun v => F₁ (v.1, v.2.1) * F₂ (v.2.2.1, v.2.2.2))
      = doubleExpectation G p F₁ * doubleExpectation G p F₂ := by
  unfold quadExpectation doubleExpectation
  rw [quadPartition_eq, doublePartition_eq]
  have hZ := partitionFunction_ne_zero G p
  have hsum : ∑ v : QuadConfig ι,
      (F₁ (v.1, v.2.1) * F₂ (v.2.2.1, v.2.2.2)) * quadWeight G p v
      = (∑ d : DoubleConfig ι, F₁ d * doubleWeight G p d) *
        ∑ d : DoubleConfig ι, F₂ d * doubleWeight G p d := by
    unfold quadWeight doubleWeight
    simp only [Fintype.sum_prod_type]
    have h4 : ∀ σ τ ρ : Config ι,
        ∑ κ : Config ι, (F₁ (σ, τ) * F₂ (ρ, κ)) *
          (boltzmannWeight G p σ * boltzmannWeight G p τ *
            boltzmannWeight G p ρ * boltzmannWeight G p κ)
        = (F₁ (σ, τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)) *
          ∑ κ : Config ι, F₂ (ρ, κ) * (boltzmannWeight G p ρ * boltzmannWeight G p κ) := by
      intro σ τ ρ
      have hgr : ∀ κ : Config ι,
          (F₁ (σ, τ) * F₂ (ρ, κ)) *
            (boltzmannWeight G p σ * boltzmannWeight G p τ *
              boltzmannWeight G p ρ * boltzmannWeight G p κ)
          = (F₁ (σ, τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)) *
            (F₂ (ρ, κ) * (boltzmannWeight G p ρ * boltzmannWeight G p κ)) :=
        fun κ => by ring
      simp_rw [hgr, ← Finset.mul_sum]
    simp_rw [h4]
    have h3 : ∀ σ τ : Config ι,
        ∑ ρ : Config ι, (F₁ (σ, τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)) *
          ∑ κ : Config ι, F₂ (ρ, κ) * (boltzmannWeight G p ρ * boltzmannWeight G p κ)
        = (F₁ (σ, τ) * (boltzmannWeight G p σ * boltzmannWeight G p τ)) *
          ∑ ρ : Config ι, ∑ κ : Config ι,
            F₂ (ρ, κ) * (boltzmannWeight G p ρ * boltzmannWeight G p κ) := by
      intro σ τ
      rw [← Finset.mul_sum]
    simp_rw [h3]
    simp_rw [← Finset.sum_mul]
  rw [hsum]
  field_simp

/-- **First-pair embedding**: a doubled observable of the first copy pair has the same
fourfold and doubled expectations. -/
theorem quadExpectation_fst_pair (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : DoubleConfig ι → ℝ) :
    quadExpectation G p (fun v => F (v.1, v.2.1)) = doubleExpectation G p F := by
  have h := quadExpectation_factor_pair G p F (fun _ => 1)
  have hone : doubleExpectation G p (fun _ => 1) = 1 := by
    unfold doubleExpectation
    rw [show ∑ d : DoubleConfig ι, (1 : ℝ) * doubleWeight G p d
        = doublePartition G p from by
      unfold doublePartition
      simp]
    field_simp [(doublePartition_pos G p).ne']
  simpa [hone] using h

/-- The site `t` variable on the doubled system: `t(i) = sign ξᵢ + sign χᵢ`. -/
noncomputable def tSite (i : ι) (d : DoubleConfig ι) : ℝ :=
  Spin.sign ℝ (d.1 i) + Spin.sign ℝ (d.2 i)

/-- The site `q` variable on the doubled system: `q(i) = sign ξᵢ − sign χᵢ`. -/
noncomputable def qSite (i : ι) (d : DoubleConfig ι) : ℝ :=
  Spin.sign ℝ (d.1 i) - Spin.sign ℝ (d.2 i)

/-- The `Finset` product of `t` variables. -/
noncomputable def tProd (A : Finset ι) (d : DoubleConfig ι) : ℝ := ∏ i ∈ A, tSite i d
/-- The `Finset` product of `q` variables. -/
noncomputable def qProd (A : Finset ι) (d : DoubleConfig ι) : ℝ := ∏ i ∈ A, qSite i d

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse rotation: the first-pair `t` is `(u₁ + u₂)/2`. -/
theorem tSite_fst_eq (i : ι) (v : QuadConfig ι) :
    tSite i (v.1, v.2.1) = (uSite₁ i v + uSite₂ i v) / 2 := by
  unfold tSite uSite₁ uSite₂ u₁ u₂ siteQuadAt s₁ s₂ s₃ s₄
  ring

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse rotation: the second-pair `t` is `(u₁ − u₂)/2`. -/
theorem tSite_snd_eq (i : ι) (v : QuadConfig ι) :
    tSite i (v.2.2.1, v.2.2.2) = (uSite₁ i v - uSite₂ i v) / 2 := by
  unfold tSite uSite₁ uSite₂ u₁ u₂ siteQuadAt s₁ s₂ s₃ s₄
  ring

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse rotation: the first-pair `q` is `(u₃ − u₄)/2`. -/
theorem qSite_fst_eq (i : ι) (v : QuadConfig ι) :
    qSite i (v.1, v.2.1) = (uSite₃ i v - uSite₄ i v) / 2 := by
  unfold qSite uSite₃ uSite₄ u₃ u₄ siteQuadAt s₁ s₂ s₃ s₄
  ring

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse rotation: the second-pair `q` is `(u₃ + u₄)/2`. -/
theorem qSite_snd_eq (i : ι) (v : QuadConfig ι) :
    qSite i (v.2.2.1, v.2.2.2) = (uSite₃ i v + uSite₄ i v) / 2 := by
  unfold qSite uSite₃ uSite₄ u₃ u₄ siteQuadAt s₁ s₂ s₃ s₄
  ring

end Lebowitz

end IsingModel
