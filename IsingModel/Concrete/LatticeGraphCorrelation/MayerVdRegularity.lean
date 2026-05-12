import IsingModel.Concrete.LatticeGraphBED
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity

/-!
# Concrete Mayer and polymer-family regularity wrappers

Narrow child module for concrete `ℤ^d` wrappers around `mayerPartialSum`,
`mayerExpansionTerm`, and `vdPolymerFamilies_sum` regularity and tanh
forwarders. This keeps callers that only need these wrappers out of the
monolithic lattice-correlation legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.6 mayerPartialSum regularity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum Continuous**. -/
theorem mayerPartialSum_Λ_latticeGraph_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) :=
  Ambient.mayerPartialSum_Λ_continuous (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: mayerPartialSum Differentiable ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_differentiable
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) :=
  Ambient.mayerPartialSum_Λ_differentiable
    (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d Λ: mayerPartialSum ContinuousOn**. -/
theorem mayerPartialSum_Λ_latticeGraph_continuousOn
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) s :=
  Ambient.mayerPartialSum_Λ_continuousOn
    (IsingModel.latticeGraph d) Λ N s

/-- **ℤ^d Λ: mayerPartialSum DifferentiableOn ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_differentiableOn
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t) s :=
  Ambient.mayerPartialSum_Λ_differentiableOn
    (IsingModel.latticeGraph d) Λ N s

/-- **ℤ^d along-ex: mayerPartialSum Continuous**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) :=
  Ambient.mayerPartialSumAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: mayerPartialSum Differentiable ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) :=
  Ambient.mayerPartialSumAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ N n

/-- **ℤ^d along-ex: mayerPartialSum ContinuousOn**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_continuousOn
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) s :=
  Ambient.mayerPartialSumAlongExhaustion_continuousOn
    (IsingModel.latticeGraph d) Λ N n s

/-- **ℤ^d along-ex: mayerPartialSum DifferentiableOn ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_differentiableOn
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t) s :=
  Ambient.mayerPartialSumAlongExhaustion_differentiableOn
    (IsingModel.latticeGraph d) Λ N n s

/-! ### §18.6 mayerExpansionTerm regularity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerExpansionTerm Continuous**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t) :=
  Ambient.mayerExpansionTerm_Λ_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d Λ: mayerExpansionTerm Differentiable ℝ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_differentiable
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t) :=
  Ambient.mayerExpansionTerm_Λ_differentiable
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerExpansionTerm Continuous**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t) :=
  Ambient.mayerExpansionTermAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ k n

/-- **ℤ^d along-ex: mayerExpansionTerm Differentiable ℝ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t) :=
  Ambient.mayerExpansionTermAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ k n

/-! ### §18.6 mayerPartialSum tanh β/J ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSum_Λ_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSum_Λ_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ N β

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSum_Λ_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSum_Λ_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ N β

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ N β n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ N β n

/-! ### §18.5 mayerExpansionTerm tanh β/J ℤ^d wraps -/

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ n J

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ n β

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ n J

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ n β

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ k J n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ k β n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ k J n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ k β n

/-! ## Moved: ℤ^d vdPolymerFamilies regularity wrappers

The 12 ℤ^d `vdPolymerFamilies_sum_Λ_latticeGraph_*` and
`vdPolymerFamilies_sumAlongExhaustion_latticeGraph_*` wrappers
(Continuous/Differentiable/HasDerivAt in t, plus tanh-variants in
β/J) now live in
`IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularityPolymer`.
The legacy import path is preserved by re-importing the new child.
-/

end Ambient
end IsingModel
