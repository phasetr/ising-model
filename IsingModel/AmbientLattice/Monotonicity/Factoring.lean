import IsingModel.AmbientLattice.Monotonicity.EdgeSiteSums

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Partition function factoring via config-equiv

Using Boltzmann factoring (PR #81) and config-equiv helpers
(PRs #82-84), express `partitionFunction extendGraph` as a product
of `partitionFunction inducedGraph Λ₁` and a complement factor. -/

/-- The complement factor used in the partition function factoring:
`F := ∑ σ₂ : (complement → Spin), exp(β·h · Σ_{v : C} sign(σ₂ v))`. -/
noncomputable def complementFactor
    {Λ₁ Λ₂ : Finset V} (_h12 : Λ₁ ⊆ Λ₂)
    (p : IsingParams ℝ) : ℝ :=
  ∑ σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin,
    Real.exp (p.β * p.h *
      ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v))

/-- **Partition function factoring**:
`Z_{extendGraphFromΛ₁} = Z_{inducedGraph Λ₁} · complementFactor`. -/
theorem partitionFunction_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction (extendGraphFromΛ₁ G Λ₁ Λ₂) p
      = partitionFunction (inducedGraph G Λ₁) p * complementFactor h12 p := by
  unfold partitionFunction complementFactor
  -- Reindex via configEquivSubtypeProd
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ)
    (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  -- Rewrite summand using Boltzmann factoring and restrict identities
  have hsum : ∀ (σ₁ : (↑Λ₁ : Type _) → Spin)
      (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin),
      boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p
        ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = boltzmannWeight (inducedGraph G Λ₁) p σ₁
        * Real.exp (p.β * p.h *
            ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v)) := by
    intro σ₁ σ₂
    simp_rw [boltzmannWeight_extendGraph_factor G h12 p,
      restrictConfig_configEquivSubtypeProd_symm,
      configEquivSubtypeProd_symm_apply_compl]
  simp_rw [hsum]
  rw [← Finset.sum_mul_sum]

/-- **Numerator factoring**: for `A ⊆ Λ₁`, the numerator for the
lifted spin product on `extendGraphFromΛ₁` equals the numerator on
`inducedGraph G Λ₁` times the complement factor. -/
theorem numerator_extendGraph_factor
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    numerator (extendGraphFromΛ₁ G Λ₁ Λ₂) p
        (spinProduct (liftFinset A (hA.trans h12)))
      = numerator (inducedGraph G Λ₁) p
          (spinProduct (liftFinset A hA))
        * complementFactor h12 p := by
  unfold numerator complementFactor
  rw [← Fintype.sum_equiv (configEquivSubtypeProd h12).symm _
    (fun σ => spinProduct (liftFinset A (hA.trans h12)) σ *
      boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p σ)
    (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  have hsum : ∀ (σ₁ : (↑Λ₁ : Type _) → Spin)
      (σ₂ : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁} → Spin),
      spinProduct (liftFinset A (hA.trans h12))
          ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
        * boltzmannWeight (extendGraphFromΛ₁ G Λ₁ Λ₂) p
            ((configEquivSubtypeProd h12).symm (σ₁, σ₂))
      = spinProduct (liftFinset A hA) σ₁
          * boltzmannWeight (inducedGraph G Λ₁) p σ₁
        * Real.exp (p.β * p.h *
            ∑ v : {x : (↑Λ₂ : Type _) // x.val ∉ Λ₁}, Spin.sign ℝ (σ₂ v)) := by
    intro σ₁ σ₂
    simp_rw [spinProduct_lift_eq h12 hA,
      boltzmannWeight_extendGraph_factor G h12 p,
      restrictConfig_configEquivSubtypeProd_symm,
      configEquivSubtypeProd_symm_apply_compl]
    ring
  simp_rw [hsum]
  rw [← Finset.sum_mul_sum]

/-- **Correlation equality**: the correlation on `extendGraphFromΛ₁`
equals the correlation on `inducedGraph G Λ₁`, when `A ⊆ Λ₁`.

Proof: the complement factor in `numerator_extendGraph_factor` and
`partitionFunction_extendGraph_factor` is identical, so it cancels
in the ratio `correlation = numerator / partitionFunction`. -/
theorem correlationΛ_extendGraph_eq
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset V} (hA : A ⊆ Λ₁) :
    correlation (extendGraphFromΛ₁ G Λ₁ Λ₂) p (liftFinset A (hA.trans h12))
      = correlation (inducedGraph G Λ₁) p (liftFinset A hA) := by
  have hZ : (0 : ℝ) < partitionFunction (inducedGraph G Λ₁) p :=
    partitionFunction_pos _ _
  have hF : (0 : ℝ) < complementFactor h12 p := by
    unfold complementFactor
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZfac := partitionFunction_extendGraph_factor G h12 p
  have hnfac := numerator_extendGraph_factor G h12 p hA
  unfold correlation
  rw [gibbsExpectation_eq_div, gibbsExpectation_eq_div, hZfac, hnfac]
  field_simp


end Ambient
end IsingModel
