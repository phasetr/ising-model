import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# Concrete Mayer analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `mayerPartialSum` and `mayerExpansionTerm`
analytic wrappers. The theorem names are the same as the former legacy
declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### `mayerPartialSum` analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum AnalyticAt ℝ**. -/
theorem mayerPartialSum_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N s) t :=
  Ambient.mayerPartialSum_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ N t

/-- **ℤ^d along-ex: mayerPartialSum AnalyticAt ℝ**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N s) t :=
  Ambient.mayerPartialSumAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ N n t

/-- **ℤ^d Λ: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSum_Λ_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d) Λ) N s) Set.univ :=
  Ambient.mayerPartialSum_Λ_analyticOnNhd
    (IsingModel.latticeGraph d) Λ N

/-- **ℤ^d along-ex: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (N : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) N s) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_analyticOnNhd
    (IsingModel.latticeGraph d) Λ N n

/-! ### `mayerExpansionTerm` analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerExpansionTerm AnalyticAt ℝ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n s) t :=
  Ambient.mayerExpansionTerm_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ n t

/-- **ℤ^d Λ: mayerExpansionTerm AnalyticOnNhd Set.univ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n s) Set.univ :=
  Ambient.mayerExpansionTerm_Λ_analyticOnNhd
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerExpansionTerm AnalyticAt ℝ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k s) t :=
  Ambient.mayerExpansionTermAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ k n t

/-- **ℤ^d along-ex: mayerExpansionTerm AnalyticOnNhd Set.univ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_analyticOnNhd
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k s)
      Set.univ :=
  Ambient.mayerExpansionTermAlongExhaustion_analyticOnNhd
    (IsingModel.latticeGraph d) Λ k n

/-! ### `mayerPartialSum` tanh β/J analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) β :=
  Ambient.mayerPartialSum_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ N J β

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) J :=
  Ambient.mayerPartialSum_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ N β J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd Set.univ
in β**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticOnNhd_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β' * J))) Set.univ :=
  Ambient.mayerPartialSum_Λ_tanh_analyticOnNhd_beta
    (IsingModel.latticeGraph d) Λ N J

/-- **ℤ^d Λ: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd Set.univ
in J**. -/
theorem mayerPartialSum_Λ_latticeGraph_tanh_analyticOnNhd_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (N : ℕ) (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J'))) Set.univ :=
  Ambient.mayerPartialSum_Λ_tanh_analyticOnNhd_J
    (IsingModel.latticeGraph d) Λ N β

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) β :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ N J β n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) J :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ N β J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd
Set.univ in β**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd
Set.univ in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J
    (IsingModel.latticeGraph d) Λ N β n

/-! ### `mayerExpansionTerm` tanh β/J analyticity ℤ^d wraps -/

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) β :=
  Ambient.mayerExpansionTerm_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ n J β

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) J :=
  Ambient.mayerExpansionTerm_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ n β J

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) β :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ k J β n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) J :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ k β J n

end Ambient
end IsingModel
