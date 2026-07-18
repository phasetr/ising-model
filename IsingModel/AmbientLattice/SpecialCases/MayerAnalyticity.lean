import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayer

/-!
# Mayer analyticity wrappers along an exhaustion

Along-exhaustion `mayerPartialSum` and `mayerExpansionTerm` analytic
wrappers, keeping callers that only need these analytic forwarders out
of the monolithic original special-cases module.

Consolidated from the former 5-module `MayerAnalyticity` family
(`MayerAnalyticity`, `MayerAnalyticityExpansionTerm`,
`MayerAnalyticityExpansionTermTanh`, `MayerAnalyticityTanh`,
`MayerAnalyticityTanhOnNhd`) — #4563 wave-2 cycle-19 fixed-cost
consolidation. All 10 theorem names/statements are preserved verbatim;
see the git history of the deleted child modules for provenance.

Contents:

* `mayerPartialSum` `AnalyticAt` / `AnalyticOnNhd` along an exhaustion;
* `mayerExpansionTerm` `AnalyticAt` / `AnalyticOnNhd` along an exhaustion;
* `mayerExpansionTerm ∘ tanh` `AnalyticAt` wrappers in `β` and `J`;
* `mayerPartialSum ∘ tanh` `AnalyticAt` wrappers in `β` and `J`;
* `mayerPartialSum ∘ tanh` `AnalyticOnNhd ℝ _ Set.univ` wrappers in `β` and `J`.

Each result is a thin pass-through of the corresponding Λ-level
`mayer*_Λ_*` analyticity lemma.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### `mayerPartialSum` analyticity along an exhaustion -/

/-- **Along-ex: `mayerPartialSum` is `AnalyticAt ℝ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) t :=
  mayerPartialSum_Λ_analyticAt G (Λ.volume n) N t

/-- **Along-ex: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N s) Set.univ :=
  mayerPartialSum_Λ_analyticOnNhd G (Λ.volume n) N

/-! ### `mayerExpansionTerm` analyticity along an exhaustion -/

/-- **Along-ex: `mayerExpansionTerm` is `AnalyticAt ℝ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) t :=
  mayerExpansionTerm_Λ_analyticAt G (Λ.volume n) k t

/-- **Along-ex: `mayerExpansionTerm` is
`AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerExpansionTermAlongExhaustion_analyticOnNhd
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k s) Set.univ :=
  mayerExpansionTerm_Λ_analyticOnNhd G (Λ.volume n) k

/-! ### `mayerExpansionTerm` tanh β/J analyticity along an exhaustion -/

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β' * J))) β :=
  mayerExpansionTerm_Λ_tanh_analyticAt_beta G (Λ.volume n) k J β

/-- **Along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerExpansionTermAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (k : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerExpansionTerm
          (inducedGraph G (Λ.volume n)) k
          (Real.tanh (β * J'))) J :=
  mayerExpansionTerm_Λ_tanh_analyticAt_J G (Λ.volume n) k β J

/-! ### `mayerPartialSum` tanh β/J analyticity along an exhaustion -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) β :=
  mayerPartialSum_Λ_tanh_analyticAt_beta G (Λ.volume n) N J β

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) J :=
  mayerPartialSum_Λ_tanh_analyticAt_J G (Λ.volume n) N β J

/-! ### `mayerPartialSum` tanh β/J `AnalyticOnNhd` along an exhaustion -/

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd in β
over `Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β' * J))) Set.univ :=
  mayerPartialSum_Λ_tanh_analyticOnNhd_beta G (Λ.volume n) N J

/-- **Along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd in J
over `Set.univ`**. -/
theorem mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.mayerPartialSum
          (inducedGraph G (Λ.volume n)) N
          (Real.tanh (β * J'))) Set.univ :=
  mayerPartialSum_Λ_tanh_analyticOnNhd_J G (Λ.volume n) N β

end Ambient
end IsingModel
