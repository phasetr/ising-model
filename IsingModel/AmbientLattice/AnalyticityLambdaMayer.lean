import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy

/-!
# AmbientLattice/Analyticity mayer wrappers

Narrow child module for 23 §18.6 mayerPartialSum_Λ + mayerExpansionTerm_Λ
continuous/differentiable/analyticAt/analyticOnNhd wrappers (raw and
tanh-composed variants). The theorem names are unchanged from the
former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.6 mayerPartialSum regularity Λ wraps -/

/-- **Λ-layer: `mayerPartialSum` is `Continuous`** (§18.6 Λ wrap). -/
theorem mayerPartialSum_Λ_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t) :=
  IsingModel.mayerPartialSum_continuous (inducedGraph G Λ) N

/-- **Λ-layer: `mayerPartialSum` is `Differentiable ℝ`** (§18.6 Λ wrap). -/
theorem mayerPartialSum_Λ_differentiable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t) :=
  IsingModel.mayerPartialSum_differentiable (inducedGraph G Λ) N

/-- **Λ-layer: `mayerPartialSum` is `AnalyticAt ℝ`** (§18.6 Λ wrap). -/
theorem mayerPartialSum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N s) t :=
  IsingModel.mayerPartialSum_analyticAt (inducedGraph G Λ) N t

/-- **Λ-layer: `mayerPartialSum` is `ContinuousOn`** (§18.6 Λ wrap of
Step 628). -/
theorem mayerPartialSum_Λ_continuousOn
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t) s :=
  IsingModel.mayerPartialSum_continuousOn (inducedGraph G Λ) N s

/-- **Λ-layer: `mayerPartialSum` is `DifferentiableOn ℝ`** (§18.6
Λ wrap of Step 628). -/
theorem mayerPartialSum_Λ_differentiableOn
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t) s :=
  IsingModel.mayerPartialSum_differentiableOn (inducedGraph G Λ) N s

/-! ### §18.6 mayerExpansionTerm regularity Λ wraps -/

/-- **Λ-layer: `mayerExpansionTerm` is `Continuous`** (§18.6 Λ wrap
of Step 588). -/
theorem mayerExpansionTerm_Λ_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t) :=
  IsingModel.mayerExpansionTerm_continuous (inducedGraph G Λ) n

/-- **Λ-layer: `mayerExpansionTerm` is `Differentiable ℝ`** (§18.6
Λ wrap of Step 589). -/
theorem mayerExpansionTerm_Λ_differentiable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t) :=
  IsingModel.mayerExpansionTerm_differentiable (inducedGraph G Λ) n

/-- **Λ-layer: `mayerExpansionTerm` is `AnalyticAt ℝ`** (§18.6 Λ
wrap of Step 590). -/
theorem mayerExpansionTerm_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n s) t :=
  IsingModel.mayerExpansionTerm_analyticAt (inducedGraph G Λ) n t

/-- **Λ-layer: `mayerExpansionTerm` is `AnalyticOnNhd ℝ _ Set.univ`**
(§18.6 Λ wrap of Step 590). -/
theorem mayerExpansionTerm_Λ_analyticOnNhd
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n s)
      Set.univ :=
  IsingModel.mayerExpansionTerm_analyticOnNhd (inducedGraph G Λ) n

/-! ### §18.6 mayerPartialSum tanh β/J Λ wraps -/

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (·*J)` continuous in β**. -/
theorem mayerPartialSum_Λ_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β' * J))) :=
  IsingModel.mayerPartialSum_tanh_continuous_beta (inducedGraph G Λ) N J

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (β*·)` continuous in J**. -/
theorem mayerPartialSum_Λ_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β * J'))) :=
  IsingModel.mayerPartialSum_tanh_continuous_J (inducedGraph G Λ) N β

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (·*J)` differentiable in β**. -/
theorem mayerPartialSum_Λ_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β' * J))) :=
  IsingModel.mayerPartialSum_tanh_differentiable_beta (inducedGraph G Λ) N J

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (β*·)` differentiable in J**. -/
theorem mayerPartialSum_Λ_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β * J'))) :=
  IsingModel.mayerPartialSum_tanh_differentiable_J (inducedGraph G Λ) N β

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (·*J)` AnalyticAt in β**. -/
theorem mayerPartialSum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β' * J))) β :=
  IsingModel.mayerPartialSum_tanh_analyticAt_beta (inducedGraph G Λ) N J β

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (β*·)` AnalyticAt in J**. -/
theorem mayerPartialSum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β * J'))) J :=
  IsingModel.mayerPartialSum_tanh_analyticAt_J (inducedGraph G Λ) N β J

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (·*J)` AnalyticOnNhd in β
over `Set.univ`**. -/
theorem mayerPartialSum_Λ_tanh_analyticOnNhd_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (J : ℝ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β' * J))) Set.univ :=
  IsingModel.mayerPartialSum_tanh_analyticOnNhd_beta (inducedGraph G Λ) N J

/-- **Λ-layer: `mayerPartialSum ∘ tanh ∘ (β*·)` AnalyticOnNhd in J
over `Set.univ`**. -/
theorem mayerPartialSum_Λ_tanh_analyticOnNhd_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (β : ℝ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum (inducedGraph G Λ) N
          (Real.tanh (β * J'))) Set.univ :=
  IsingModel.mayerPartialSum_tanh_analyticOnNhd_J (inducedGraph G Λ) N β

/-! ### §18.5 mayerExpansionTerm tanh β/J Λ wraps -/

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTerm_Λ_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β' * J))) :=
  IsingModel.mayerExpansionTerm_tanh_continuous_beta (inducedGraph G Λ) n J

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTerm_Λ_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β * J'))) :=
  IsingModel.mayerExpansionTerm_tanh_continuous_J (inducedGraph G Λ) n β

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTerm_Λ_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β' * J))) :=
  IsingModel.mayerExpansionTerm_tanh_differentiable_beta (inducedGraph G Λ) n J

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTerm_Λ_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β * J'))) :=
  IsingModel.mayerExpansionTerm_tanh_differentiable_J (inducedGraph G Λ) n β

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTerm_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β' * J))) β :=
  IsingModel.mayerExpansionTerm_tanh_analyticAt_beta (inducedGraph G Λ) n J β

/-- **Λ-layer: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTerm_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) n
          (Real.tanh (β * J'))) J :=
  IsingModel.mayerExpansionTerm_tanh_analyticAt_J (inducedGraph G Λ) n β J


end Ambient

end IsingModel
