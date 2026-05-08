import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer and polymer-family regularity wrappers along an exhaustion

Narrow child module for along-exhaustion `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum` regularity and tanh
wrappers. This keeps callers that only need these forwarders out of the
monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 mayerPartialSum regularity along-ex wraps -/

/-- **Along-ex: `mayerPartialSum` is `Continuous`**. -/
theorem mayerPartialSumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_continuous G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `Differentiable ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) :=
  mayerPartialSum_Λ_differentiable G (Λ.volume n) N

/-- **Along-ex: `mayerPartialSum` is `ContinuousOn`**. -/
theorem mayerPartialSumAlongExhaustion_continuousOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_continuousOn G (Λ.volume n) N s

/-- **Along-ex: `mayerPartialSum` is `DifferentiableOn ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_differentiableOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N t) s :=
  mayerPartialSum_Λ_differentiableOn G (Λ.volume n) N s

/-! ### §18.6 mayerExpansionTerm regularity along-ex wraps -/

/-- **Along-ex: `mayerExpansionTerm` is `Continuous`**. -/
theorem mayerExpansionTermAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_continuous G (Λ.volume n) k

/-- **Along-ex: `mayerExpansionTerm` is `Differentiable ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k t) :=
  mayerExpansionTerm_Λ_differentiable G (Λ.volume n) k

/-! ### §18.6 mayerPartialSum tanh β/J along-ex wraps -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_continuous_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_continuous_J G (Λ.volume n) N β

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) :=
  mayerPartialSum_Λ_tanh_differentiable_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) :=
  mayerPartialSum_Λ_tanh_differentiable_J G (Λ.volume n) N β

/-! ### §18.5 mayerExpansionTerm tanh β/J along-ex wraps -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_continuous_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_continuous_J G (Λ.volume n) k β

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_beta G (Λ.volume n) k J

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) :=
  mayerExpansionTerm_Λ_tanh_differentiable_J G (Λ.volume n) k β

/-! ### §18.6 vdPolymerFamilies_sum regularity in t along-ex wraps -/

/-- **Along-ex: `vdPolymerFamilies_sum` is `Continuous` in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_continuous G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` is `Differentiable ℝ`
in `t`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_differentiable
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_differentiable G (Λ.volume n)

/-- **Along-ex: `vdPolymerFamilies_sum` `HasDerivAt`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  vdPolymerFamilies_sum_Λ_hasDerivAt G (Λ.volume n) t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J along-ex wraps -/

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_continuous_J G (Λ.volume n) β

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_beta G (Λ.volume n) J

/-- **Along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  vdPolymerFamilies_sum_Λ_tanh_differentiable_J G (Λ.volume n) β

end Ambient
end IsingModel
