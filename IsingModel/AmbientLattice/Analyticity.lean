import IsingModel.AmbientLattice.Defs
import IsingModel.ClusterExpansion

/-!
# Joint analyticity for AmbientLattice finite-volume Λ-restricted Ising

Lifts the joint analyticity of `partitionFunction` and `freeEnergy` in
`(β, J, h) ∈ ℝ × ℝ × ℝ` (Glimm-Jaffe §18.6 capstone, established in
`IsingModel/ClusterExpansion.lean` via direct sum-of-exp analyticity)
to the finite-volume Λ-restricted versions defined in
`IsingModel/AmbientLattice/Defs.lean`. Each theorem is a thin wrapper
around the corresponding theorem on `inducedGraph G Λ`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **partitionFunctionΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, Λ-layer): direct lift of `IsingModel.partitionFunction_analyticAt_joint`
to the finite-volume Λ-restricted partition function. -/
theorem partitionFunctionΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) :=
  IsingModel.partitionFunction_analyticAt_joint (inducedGraph G Λ) β J h

/-- **partitionFunctionΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`**
(§18.6 capstone, Λ-layer). -/
theorem partitionFunctionΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  IsingModel.partitionFunction_analyticOnNhd_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6
capstone, Λ-layer): direct lift of `IsingModel.freeEnergy_analyticAt_joint`
to the finite-volume Λ-restricted free energy. -/
theorem freeEnergyΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      (β, J, h) :=
  IsingModel.freeEnergy_analyticAt_joint (inducedGraph G Λ) β J h

/-- **freeEnergyΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6
capstone, Λ-layer). -/
theorem freeEnergyΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩)
      Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `Continuous` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem freeEnergyΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) :=
  IsingModel.freeEnergy_continuous_joint (inducedGraph G Λ)

/-- **freeEnergyΛ jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem freeEnergyΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => freeEnergyΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) :=
  IsingModel.freeEnergy_differentiable_joint (inducedGraph G Λ)

/-- **correlationΛ jointly `AnalyticAt ℝ` in `(β, J, h)`** (§18.6,
Λ-layer): direct lift of `IsingModel.correlation_analyticAt_joint`. -/
theorem correlationΛ_analyticAt_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) (β J h : ℝ) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A)
      (β, J, h) :=
  IsingModel.correlation_analyticAt_joint (inducedGraph G Λ) A β J h

/-- **correlationΛ jointly `AnalyticOnNhd ℝ` over `Set.univ`** (§18.6,
Λ-layer). -/
theorem correlationΛ_analyticOnNhd_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A)
      Set.univ :=
  IsingModel.correlation_analyticOnNhd_joint (inducedGraph G Λ) A

/-- **correlationΛ jointly `Continuous` in `(β, J, h)`** (§18.6, Λ-layer). -/
theorem correlationΛ_continuous_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    Continuous (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  IsingModel.correlation_continuous_joint (inducedGraph G Λ) A

/-- **correlationΛ jointly `Differentiable ℝ` in `(β, J, h)`** (§18.6,
Λ-layer). -/
theorem correlationΛ_differentiable_joint (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (A : Finset (↑Λ : Type _)) :
    Differentiable ℝ
      (fun p : ℝ × ℝ × ℝ => correlationΛ G Λ ⟨p.2.1, p.2.2, p.1⟩ A) :=
  IsingModel.correlation_differentiable_joint (inducedGraph G Λ) A

/-! ## Λ-layer partitionFunction per-direction regularity at general h -/

/-- **partitionFunctionΛ Continuous in `β` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_beta_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Continuous (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) :=
  IsingModel.partitionFunction_continuous_beta_general_h (inducedGraph G Λ) J h

/-- **partitionFunctionΛ Differentiable in `β` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_beta_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    Differentiable ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) :=
  IsingModel.partitionFunction_differentiable_beta_general_h (inducedGraph G Λ) J h

/-- **partitionFunctionΛ Continuous in `J` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_J_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    Continuous (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) :=
  IsingModel.partitionFunction_continuous_J_general_h (inducedGraph G Λ) β h

/-- **partitionFunctionΛ Differentiable in `J` at general h** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_J_general_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    Differentiable ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) :=
  IsingModel.partitionFunction_differentiable_J_general_h (inducedGraph G Λ) β h

/-- **partitionFunctionΛ Continuous in `h`** (Λ-layer). -/
theorem partitionFunctionΛ_continuous_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Continuous (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) :=
  IsingModel.partitionFunction_continuous_h (inducedGraph G Λ) J β

/-- **partitionFunctionΛ Differentiable in `h`** (Λ-layer). -/
theorem partitionFunctionΛ_differentiable_h (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Differentiable ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) :=
  IsingModel.partitionFunction_differentiable_h (inducedGraph G Λ) J β

/-! ## §18.4 polymerFreeEnergy / vdSum / ε iff Λ-layer wrappers

Direct lifts of the iff / strict-mono / strict-pos GJ-命題-bundle from
`IsingModel/ClusterExpansion.lean` (PRs #1547-#1562) to the
finite-volume Λ-restricted setting via `inducedGraph G Λ`. -/

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: `polymerFreeEnergy` strictly increasing under polymers
exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) s <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: `polymerFreeEnergy_strictMonoOn (Set.Ici 0)` under
polymers exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy (inducedGraph G Λ) t)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: `polymerFreeEnergy > 0 ↔ 0 < t ∧ polymers exist`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < t ∧ (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_pos_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy = 0 ↔ t = 0 ∨ no polymers`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_eq_zero_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ ε(t)` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_eps_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_le_eps_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < ε(t)` when `ε(t) > 0`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_eps_pos : 0 < ∑ Γ ∈
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_of_eps_pos (inducedGraph G Λ) h_eps_pos

/-- **Λ-layer: `polymerFreeEnergy ≤ (1+t)^|E| - 1` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_pow_sub_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_le_pow_sub_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < log 2` under `(1+t)^|E| < 2` and
`0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_lt_log_two_of_pow_lt_two (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: `vdSum > 1 ↔ ε > 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_gt_one_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: `vdSum = 1 ↔ ε = 0`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_eq_one_iff_eps_eq_zero (inducedGraph G Λ) t

/-! ### §18.4 mayerExpansionTerm / mayerPartialSum Λ-layer wrappers -/

/-- **Λ-layer: `mayerExpansionTerm = 0` for graphs with no polymers** (§18.4 Λ wrap). -/
theorem mayerExpansionTerm_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅) (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t = 0 :=
  IsingModel.mayerExpansionTerm_eq_zero_of_no_polymers (inducedGraph G Λ) h_no n t

/-- **Λ-layer: `mayerPartialSum G 0 t = 0`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_zero_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero_eq_zero (inducedGraph G Λ) t

/-- **Λ-layer: `mayerPartialSum G 1 t > 0` under `0 < t` and polymers exist**
(§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: `mayerPartialSum G 1 t ≥ 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_nonneg_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `mayerExpansionTerm` filter to connected polymer
sequences** (§18.4 Λ wrap of PR #1521). -/
theorem mayerExpansionTerm_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t =
      ∑ ω ∈ (Fintype.piFinset
          (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
        IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerExpansionTerm_filter_connected (inducedGraph G Λ) n t

/-- **Λ-layer: `mayerPartialSum` filter to connected polymer sequences**
(§18.4 Λ wrap of PR #1522). -/
theorem mayerPartialSum_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ω ∈ (Fintype.piFinset
            (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
          IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerPartialSum_filter_connected (inducedGraph G Λ) N t

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`** (§18.4 Λ wrap of PR #1526). -/
theorem polymerFreeEnergy_Λ_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_high_temp_sandwich (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`**
(§18.4 Λ wrap of PR #1517). -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_high_temp_sandwich`). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two`). -/
theorem polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich** (§18.5 Λ wrap of
`vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich (inducedGraph G Λ) hβJ

/-- **Λ-layer: VD polymer-family sum sharp sandwich** (§18.5 Λ wrap
of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: log Taylor expansion for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem
polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich (ferromagnetic)**
(§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: strict `freeEnergyΛ` upper bound in cluster-expansion
convergence regime** (§18.5 Λ wrap of #1527). -/
theorem freeEnergyΛ_lt_log_two_plus_high_temp_correction
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card := by
  rw [freeEnergyΛ_apply]
  have hne' : 0 < Fintype.card ↑Λ := by rw [Fintype.card_coe]; exact hne
  have := IsingModel.freeEnergy_lt_log_two_plus_high_temp_correction
    (inducedGraph G Λ) J β hβJ hne' h_pow
  rwa [Fintype.card_coe] at this

/-- **Λ-layer: strict `freeEnergyΛ` upper bound in cluster-expansion
convergence regime (ferromagnetic)** (§18.5 Λ wrap, ferro). -/
theorem freeEnergyΛ_lt_log_two_plus_high_temp_correction_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) <
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) / Λ.card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / Λ.card :=
  freeEnergyΛ_lt_log_two_plus_high_temp_correction
    G Λ J β (mul_nonneg hβ.le hJ) hne h_pow

/-- **Λ-layer: `polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`**
(§18.5 Λ wrap of #1517 / Step 611). -/
theorem polymerFreeEnergy_Λ_continuousAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_continuousAt (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_differentiableAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_differentiableAt (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `ContinuousOn (Set.Ici 0)`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_continuousOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ContinuousOn (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_continuousOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy` is `DifferentiableOn (Set.Ici 0)`**
(§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_differentiableOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) s)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_differentiableOn_Ici_zero
    (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (·*J)` `AnalyticAt ℝ`
in β** (§18.6 Λ wrap of #1569 Step 613). -/
theorem polymerFreeEnergy_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β' * J))) β :=
  IsingModel.polymerFreeEnergy_tanh_analyticAt_beta
    (inducedGraph G Λ) J β hβJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (β*·)` `AnalyticAt ℝ`
in J** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J'))) J :=
  IsingModel.polymerFreeEnergy_tanh_analyticAt_J
    (inducedGraph G Λ) β J hβJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (·*J)` `AnalyticOnNhd
ℝ _ (Set.Ici 0)` in β under `0 ≤ J`** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β' * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_analyticOnNhd_beta_Ici_zero
    (inducedGraph G Λ) hJ

/-- **Λ-layer: `polymerFreeEnergy ∘ tanh ∘ (β*·)` `AnalyticOnNhd
ℝ _ (Set.Ici 0)` in J under `0 ≤ β`** (§18.6 Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J'))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_analyticOnNhd_J_Ici_zero
    (inducedGraph G Λ) hβ

/-- **Λ-layer: `polymerFreeEnergy ≥ 0` under `t ≥ 0`** (§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ |E| · log(1 + t)` under
`t ≥ 0`** (§18.5 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_card_log_one_plus_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log (1 + t) :=
  IsingModel.polymerFreeEnergy_le_card_log_one_plus_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`**
(§18.5 Λ wrap of Step 634). -/
theorem polymerFreeEnergy_Λ_le_card_mul_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * t :=
  IsingModel.polymerFreeEnergy_le_card_mul_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy` is `MonotoneOn (Set.Ici 0)`**
(§18.5 Λ wrap of Step 633). -/
theorem polymerFreeEnergy_Λ_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    MonotoneOn (fun t : ℝ =>
        IsingModel.polymerFreeEnergy (inducedGraph G Λ) t)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_monotoneOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: `polymerFreeEnergy = 0` for empty-polymer induced
graphs** (§18.5 Λ wrap of Step 621). -/
theorem polymerFreeEnergy_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_of_no_polymers
    (inducedGraph G Λ) h_no t

/-- **Λ-layer: `polymerFreeEnergy = 0` for edgeless induced graphs**
(§18.5 Λ wrap of Step 623). -/
theorem polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t

/-- **Λ-layer: `polymerFreeEnergy` preserves order on `[0, ∞)`**
(§18.5 Λ wrap of Step 649). -/
theorem polymerFreeEnergy_Λ_le_of_le_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) s :=
  IsingModel.polymerFreeEnergy_le_of_le_of_nonneg
    (inducedGraph G Λ) ht hs hts

/-- **Λ-layer: `polymerFreeEnergy` strict-form order preservation**
(§18.5 Λ wrap of Step 650). -/
theorem polymerFreeEnergy_Λ_le_of_le_strict_form
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) s :=
  IsingModel.polymerFreeEnergy_le_of_le_strict_form
    (inducedGraph G Λ) ht hts

/-- **Λ-layer: `polymerFreeEnergy` tanh-form sandwich** (§18.5 Λ wrap
of Step 632). -/
theorem polymerFreeEnergy_Λ_tanh_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_sandwich (inducedGraph G Λ) hβJ

/-- **Λ-layer: `polymerFreeEnergy ≤ |E|·log 2` for `0 ≤ t ≤ 1`**
(§18.5 Λ wrap of Step 642). -/
theorem polymerFreeEnergy_Λ_le_card_log_two_of_le_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_le_card_log_two_of_le_one
    (inducedGraph G Λ) ht ht1

/-- **Λ-layer: `polymerFreeEnergy_tanh ≤ |E|·log 2` under `0 ≤ β·J`**
(§18.5 Λ wrap of Step 643). -/
theorem polymerFreeEnergy_Λ_tanh_le_card_log_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_le_card_log_two
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: `polymerFreeEnergy_tanh` double bound** (§18.5 Λ wrap
of Step 645). -/
theorem polymerFreeEnergy_Λ_tanh_double_bound
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_double_bound
    (inducedGraph G Λ) hβJ

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

/-! ### §18.6 vdPolymerFamilies_sum regularity in t Λ wraps -/

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Continuous` in `t`** (§18.6). -/
theorem vdPolymerFamilies_sum_Λ_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_continuous (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `Differentiable ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_differentiable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_differentiable (inducedGraph G Λ)

/-- **Λ-layer: `vdPolymerFamilies_sum` is `AnalyticAt ℝ` in `t`**. -/
theorem vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) t

/-- **Λ-layer: `vdPolymerFamilies_sum` `HasDerivAt` (explicit
polynomial derivative)**. -/
theorem vdPolymerFamilies_sum_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, s ^ P.card)
      (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
          ((Q.card : ℝ) * t ^ (Q.card - 1))) t :=
  IsingModel.vdPolymerFamilies_sum_hasDerivAt (inducedGraph G Λ) t

/-! ### §18.5 vdPolymerFamilies_sum tanh β/J Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_beta (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_continuous_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_continuous_J (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_beta
    (inducedGraph G Λ) J

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_differentiable_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_differentiable_J
    (inducedGraph G Λ) β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β

/-- **Λ-layer: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  IsingModel.vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J

/-! ### §18.5 log_vdPolymerFamilies_sum analyticity Λ wraps -/

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticAt for `t ≥ 0`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) t :=
  IsingModel.log_vdPolymerFamilies_sum_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: `log_vdPolymerFamilies_sum` AnalyticOnNhd over `[0, ∞)`**. -/
theorem log_vdPolymerFamilies_sum_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ), ∏ P ∈ Γ, s ^ P.card)) (Set.Ici 0) :=
  IsingModel.log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero
    (inducedGraph G Λ)

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in β under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card)) β :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_beta
    (inducedGraph G Λ) J β hβJ

/-- **Λ-layer: log_vdPolymerFamilies_sum ∘ tanh AnalyticAt in J under
`0 ≤ β·J`**. -/
theorem log_vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ =>
        Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card)) J :=
  IsingModel.log_vdPolymerFamilies_sum_tanh_analyticAt_J
    (inducedGraph G Λ) β J hβJ

/-! ### §18.5 mayer_identity_at edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity at `t = 0`** (Step 600). -/
theorem mayer_identity_at_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, (0 : ℝ) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.mayer_identity_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: Mayer identity at `β·J = 0`** (Step 609). -/
theorem mayer_identity_at_betaJ_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_at_betaJ_zero (inducedGraph G Λ) hβJ N

/-- **Λ-layer: Mayer identity at `β = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_beta_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh ((0 : ℝ) * J) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = 0`** (Step 609 specialisation). -/
theorem mayer_identity_at_J_zero_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    Real.log (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ),
              ∏ P ∈ Γ, Real.tanh (β * (0 : ℝ)) ^ P.card) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero (inducedGraph G Λ) β N

/-! ### §18.5 polymerFreeEnergy_eq_mayerPartialSum_at edge-case Λ wraps -/

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at t = 0**
(Step 611). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_zero
    (inducedGraph G Λ) N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β·J = 0**
(Step 617). -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    (inducedGraph G Λ) hβJ N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at β = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    (inducedGraph G Λ) J N

/-- **Λ-layer: polymerFreeEnergy = mayerPartialSum at J = 0**. -/
theorem polymerFreeEnergy_Λ_eq_mayerPartialSum_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    (inducedGraph G Λ) β N

/-! ### §18.5 mayer_identity polymer_free_energy variants Λ wraps -/

/-- **Λ-layer: Mayer identity at `J = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_J_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_J_zero_polymer_free_energy
    (inducedGraph G Λ) β N

/-- **Λ-layer: Mayer identity at `β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_beta_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * J)) :=
  IsingModel.mayer_identity_at_beta_zero_polymer_free_energy
    (inducedGraph G Λ) J N

/-- **Λ-layer: Mayer identity at `J = β = 0` (polymer_free_energy form)**. -/
theorem mayer_identity_at_either_zero_polymer_free_energy_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  IsingModel.mayer_identity_at_either_zero_polymer_free_energy
    (inducedGraph G Λ) N

/-! ### §18.5 mayerPartialSum_zero ≤ polymerFreeEnergy Λ wraps -/

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy under `t ≥ 0`**. -/
theorem mayerPartialSum_zero_Λ_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.mayerPartialSum_zero_le_polymerFreeEnergy
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerPartialSum 0 ≤ polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic mayerPartialSum 0 ≤
polymerFreeEnergy(tanh(β·J))**. -/
theorem mayerPartialSum_zero_Λ_tanh_le_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0
        (Real.tanh (β * J)) ≤
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) :=
  IsingModel.mayerPartialSum_zero_tanh_le_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-! ### §18.5 mayer_identity_of edge-case Λ wraps -/

/-- **Λ-layer: Mayer identity for empty-polymer graphs**. -/
theorem mayer_identity_of_no_polymers_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_no_polymers (inducedGraph G Λ) h_no t N

/-- **Λ-layer: Mayer identity for empty-polymer graphs (tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_no_polymers_tanh
    (inducedGraph G Λ) h_no β J N

/-- **Λ-layer: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers (inducedGraph G Λ) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_trivial (inducedGraph G Λ) h N

/-- **Λ-layer: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayer_identity_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: Mayer identity for edgeless induced graphs (tanh form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N
        (Real.tanh (β * J)) :=
  IsingModel.mayer_identity_of_edgeFinset_empty_tanh
    (inducedGraph G Λ) h_empty β J N

/-! ### §18.5 basic identities at_zero / at_one Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  IsingModel.vdPolymerFamilies_sum_at_zero (inducedGraph G Λ)

/-- **Λ-layer: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly families**. -/
theorem vdPolymerFamilies_sum_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).card :=
  IsingModel.vdPolymerFamilies_sum_at_one (inducedGraph G Λ)

/-- **Λ-layer: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSum_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerPartialSum_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 = 0 :=
  IsingModel.mayerPartialSum_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerExpansionTerm_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTerm_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerExpansionTerm_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n 0 = 0 :=
  IsingModel.mayerExpansionTerm_at_zero (inducedGraph G Λ) n

/-! ### §18.5 vdPolymerFamilies_sum tanh iff characterizations Λ wraps -/

/-- **Λ-layer: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum bound family Λ-layer wraps -/

/-- **Λ-layer: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_two_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_two_pow (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_tanh_pow
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  IsingModel.one_le_vdPolymerFamilies_sum (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds Λ-layer -/

/-- **Λ-layer: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_ge_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_pos_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_eq_one_add
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_eq_one_add (inducedGraph G Λ) t

/-! ### §18.5 Mayer expansion edge-cases + n=2 + abs_le Λ-layer -/

/-- **Λ-layer: mayerExpansionTerm at `n = 2`**. -/
theorem mayerExpansionTerm_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      ∑ pq ∈ (IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
              (IsingModel.allPolymers (inducedGraph G Λ)),
        (if IsingModel.PolymersIncompatible pq.1 pq.2 then (-1/2 : ℝ)
          else 0) *
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at `n = 2`, filter form**. -/
theorem mayerExpansionTerm_Λ_two_filter
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t =
      (-1/2 : ℝ) *
        ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                (IsingModel.allPolymers (inducedGraph G Λ))).filter
            (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
          (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerExpansionTerm_two_filter (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at `N = 2`**. -/
theorem mayerPartialSum_Λ_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 2 t =
      (∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((IsingModel.allPolymers (inducedGraph G Λ)) ×ˢ
                  (IsingModel.allPolymers (inducedGraph G Λ))).filter
              (fun pq => IsingModel.PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) :=
  IsingModel.mayerPartialSum_two (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum = 0 on no-polymer graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_no_polymers
    (inducedGraph G Λ) h_no t N

/-- **Λ-layer: mayerPartialSum = 0 on edgeless graphs**. -/
theorem mayerPartialSum_Λ_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t = 0 :=
  IsingModel.mayerPartialSum_eq_zero_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty t N

/-- **Λ-layer: mayerExpansionTerm absolute bound**. -/
theorem mayerExpansionTerm_Λ_abs_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) (t : ℝ) :
    |IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t| ≤
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ)),
        |IsingModel.ursellCoefficient ω| *
          |IsingModel.clusterSeqActivity t ω| :=
  IsingModel.mayerExpansionTerm_abs_le (inducedGraph G Λ) n t

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + analytic + sandwich Λ -/

/-- **Λ-layer: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergy_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 0 = 0 :=
  IsingModel.polymerFreeEnergy_at_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergy_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ)).card :=
  IsingModel.polymerFreeEnergy_at_one (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) t :=
  IsingModel.polymerFreeEnergy_analyticAt (inducedGraph G Λ) ht

/-- **Λ-layer: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G Λ) s) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_analyticOnNhd_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log (1 + t) :=
  IsingModel.polymerFreeEnergy_sandwich_of_nonneg (inducedGraph G Λ) ht

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add Λ-layer wraps -/

/-- **Λ-layer: polymerFreeEnergy tanh ≤ |E| · tanh** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul (inducedGraph G Λ) hβJ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_le_card_mul**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_mul_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.tanh (β * J) :=
  IsingModel.polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh_sandwich**. -/
theorem polymerFreeEnergy_Λ_tanh_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: ferromagnetic polymerFreeEnergy_tanh ≤ |E| · log 2**. -/
theorem polymerFreeEnergy_Λ_tanh_le_card_log_two_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (inducedGraph G Λ).edgeFinset.card * Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergy_Λ_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.polymerFreeEnergy_eq_log_one_add_eps (inducedGraph G Λ) t

/-- **Λ-layer: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_hasDerivAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  IsingModel.polymerFreeEnergy_hasDerivAt (inducedGraph G Λ) ht

/-! ### §18.5 Mayer recurrence + hasSum + tendsto Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum recurrence** in `N`. -/
theorem mayerPartialSum_Λ_succ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) N t +
        IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t :=
  IsingModel.mayerPartialSum_succ (inducedGraph G Λ) N t

/-- **Λ-layer: mayerExpansionTerm = mayerPartialSum diff**. -/
theorem mayerExpansionTerm_Λ_eq_mayerPartialSum_diff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) (N + 1) t =
      IsingModel.mayerPartialSum (inducedGraph G Λ) (N + 1) t -
        IsingModel.mayerPartialSum (inducedGraph G Λ) N t :=
  IsingModel.mayerExpansionTerm_eq_mayerPartialSum_diff
    (inducedGraph G Λ) N t

/-- **Λ-layer: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log (inducedGraph G Λ) h_abs

/-- **Λ-layer: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G Λ)).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) → 0 as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tendsto_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tendsto_zero
    (inducedGraph G Λ)

/-! ### §18.5 ε(t) infrastructure + Mayer term sign + allPolymers
empty Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ mayerExpansionTerm at n = 1** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t :=
  IsingModel.mayerExpansionTerm_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: mayerExpansionTerm at n = 2 ≤ 0** under `0 ≤ t`. -/
theorem mayerExpansionTerm_Λ_two_nonpos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 2 t ≤ 0 :=
  IsingModel.mayerExpansionTerm_two_nonpos_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0) = 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_at_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_continuous
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_continuous
    (inducedGraph G Λ)

/-- **Λ-layer: ε(t) is `AnalyticAt ℝ` at every `t`**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_analyticAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t :=
  IsingModel.vdPolymerFamilies_sum_minus_one_analyticAt
    (inducedGraph G Λ) t

/-- **Λ-layer: ε(t) < 1 eventually as t → 0**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_lt_one_eventually
    (inducedGraph G Λ)

/-- **Λ-layer: allPolymers = ∅ on edgeless induced graphs**. -/
theorem allPolymers_Λ_eq_empty_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_empty : (inducedGraph G Λ).edgeFinset = ∅) :
    IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.allPolymers_eq_empty_of_edgeFinset_empty
    (inducedGraph G Λ) h_empty

/-! ### §18.5 ε(t) / polymerFreeEnergy positivity-iff Λ-layer wraps -/

/-- **Λ-layer: 0 < ε(t) ↔ 0 < t ∧ allPolymers ≠ ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < t ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(t) = 0 ↔ t = 0 ∨ allPolymers = ∅** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_eq_zero_iff
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < ε(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** under
`0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: ε(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < polymerFreeEnergy(tanh) ↔ 0 < tanh ∧
allPolymers ≠ ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff (inducedGraph G Λ) hβJ

/-- **Λ-layer: polymerFreeEnergy(tanh) = 0 ↔ tanh = 0 ∨
allPolymers = ∅** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 strict-mono / strict-pos under polymers ≠ ∅
Λ-layer wraps -/

/-- **Λ-layer: vdSum(s) < vdSum(t) for `0 ≤ s < t`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, s ^ P.card) <
      ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ici 0)`** under polymers
exist. -/
theorem vdPolymerFamilies_sum_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: 0 < pFE under `0 < t` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 1 < vdSum under `0 < t` and polymers exist**. -/
theorem vdPolymerFamilies_sum_Λ_gt_one_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_gt_one_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < ε(t) under `0 < t` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: 0 < pFE(tanh) under `0 < tanh` and polymers exist**. -/
theorem polymerFreeEnergy_Λ_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) :=
  IsingModel.polymerFreeEnergy_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 1 < vdSum(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: 0 < ε(tanh) under `0 < tanh` and polymers exist**. -/
theorem
vdPolymerFamilies_sum_Λ_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (h_tanh_pos : 0 < Real.tanh (β * J))
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :=
  IsingModel.vdPolymerFamilies_sum_minus_one_tanh_pos_of_tanh_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_tanh_pos h_poly

/-- **Λ-layer: pFE is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem polymerFreeEnergy_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) t) (Set.Ioi 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: vdSum is `StrictMonoOn (Set.Ioi 0)`** under polymers
exist. -/
theorem
vdPolymerFamilies_sum_Λ_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ioi 0) :=
  IsingModel.vdPolymerFamilies_sum_strictMonoOn_Ioi_zero_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
Λ-layer wraps (under `0 ≤ β, 0 ≤ J`) -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) < (1 + tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-! ### §18.5 polymerFreeEnergy tanh sharpening + β/J strict-mono
Λ-layer wraps -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** under `0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(`0 ≤ β·J`). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) hβJ h_eps_pos

/-- **Λ-layer: pFE(tanh(β₁·J)) < pFE(tanh(β₂·J))** under `J > 0`,
`0 ≤ β₁ < β₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β₁ β₂ J : ℝ} (hβ₁ : 0 ≤ β₁) (hJ : 0 < J) (hβ : β₁ < β₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₁ * J)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β₂ * J)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ₁ hJ hβ

/-- **Λ-layer: pFE(tanh(β·J₁)) < pFE(tanh(β·J₂))** under `β > 0`,
`0 ≤ J₁ < J₂`, polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hβ : 0 < β) (hJ : J₁ < J₂) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₁)) <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J₂)) :=
  IsingModel.polymerFreeEnergy_tanh_lt_of_lt_in_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ₁ hβ hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in β**
under `J > 0` and polymers nonempty. -/
theorem
polymerFreeEnergy_Λ_tanh_strictMonoOn_beta_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    StrictMonoOn (fun β : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_beta_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hJ

/-- **Λ-layer: pFE(tanh(β·J)) is `StrictMonoOn (Set.Ici 0)` in J**
under `β > 0` and polymers nonempty. -/
theorem polymerFreeEnergy_Λ_tanh_strictMonoOn_J_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    StrictMonoOn (fun J : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G Λ) (Real.tanh (β * J))) (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_tanh_strictMonoOn_J_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hβ

/-! ### §18.5 ε(t) nonneg + non-tanh polymerFreeEnergy sharpening
Λ-layer wraps -/

/-- **Λ-layer: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow_at_zero
    (inducedGraph G Λ) hn

/-- **Λ-layer: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_eq_zero_iff_eps_eq_zero
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_pos_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_iff_eps_pos
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_lt_pow_sub_one_of_eps_pos
    (inducedGraph G Λ) ht h_eps_pos

/-! ### §18.5 vdSum sandwich/monotone + ε bound + pFE(tanh) bound +
log2 Λ-layer wraps -/

/-- **Λ-layer: vdSum sandwich for `t ≥ 0`**: `1 ≤ vdSum ≤
(1+t)^|E|`. -/
theorem vdPolymerFamilies_sum_Λ_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  IsingModel.vdPolymerFamilies_sum_monotoneOn_Ici_zero (inducedGraph G Λ)

/-- **Λ-layer: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.vdPolymerFamilies_sum_minus_one_le_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: pFE(tanh) ≤ ε(tanh) under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_eps_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_le_eps_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) ≤ (1+tanh)^|E| - 1 under `0 ≤ β·J`**. -/
theorem polymerFreeEnergy_Λ_tanh_le_pow_sub_one_of_betaJ_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_le_pow_sub_one_of_betaJ_nonneg
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: pFE(tanh) < log 2** under `(1+tanh)^|E| < 2` and
`0 ≤ β·J`. -/
theorem polymerFreeEnergy_Λ_tanh_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_lt_log_two_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow

/-! ### §18.6 partitionFunctionΛ regularity at `h = 0` Λ-layer wraps -/

/-- **Λ-layer: partitionFunction Continuous in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Continuous in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_continuous_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction Differentiable in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    Differentiable ℝ
      (fun β : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction Differentiable in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_differentiable_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    Differentiable ℝ
      (fun J : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_J_h_zero
    (inducedGraph G Λ) β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_h_zero
    (inducedGraph G Λ) J β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem partitionFunctionΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_h_zero
    (inducedGraph G Λ) β J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, 0, β'⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_beta_h_zero
    (inducedGraph G Λ) J

/-- **Λ-layer: partitionFunction `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem partitionFunctionΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', 0, β⟩) Set.univ := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticOnNhd_J_h_zero
    (inducedGraph G Λ) β

/-! ### §18.6 freeEnergyΛ per-direction analyticity Λ-layer wraps -/

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_h_zero (inducedGraph G Λ) J β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at `h = 0`**. -/
theorem freeEnergyΛ_analyticAt_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_h_zero (inducedGraph G Λ) β J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, 0, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_h_zero (inducedGraph G Λ) J

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at `h = 0`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_h_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', 0, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_h_zero (inducedGraph G Λ) β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `β` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) β :=
  IsingModel.freeEnergy_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `J` at general `h`**. -/
theorem freeEnergyΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) J :=
  IsingModel.freeEnergy_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: freeEnergy `AnalyticAt ℝ` in `h`**. -/
theorem freeEnergyΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) h :=
  IsingModel.freeEnergy_analyticAt_h (inducedGraph G Λ) J β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h : ℝ) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => freeEnergyΛ G Λ ⟨J, h, β'⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_beta_general_h
    (inducedGraph G Λ) J h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J` at
general `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h : ℝ) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => freeEnergyΛ G Λ ⟨J', h, β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_J_general_h
    (inducedGraph G Λ) β h

/-- **Λ-layer: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyΛ_analyticOnNhd_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    AnalyticOnNhd ℝ
      (fun h' : ℝ => freeEnergyΛ G Λ ⟨J, h', β⟩) Set.univ :=
  IsingModel.freeEnergy_analyticOnNhd_h (inducedGraph G Λ) J β

/-! ### §18.6 partitionFunction joint + general-h analyticity
Λ-layer wraps -/

/-- **Λ-layer: partitionFunction jointly `Continuous` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_continuous_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_continuous_joint (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction jointly `Differentiable ℝ` in
`(β, J, h)`**. -/
theorem partitionFunctionΛ_differentiable_joint
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionΛ G Λ ⟨p.2.1, p.2.2, p.1⟩) := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_differentiable_joint
    (inducedGraph G Λ)

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `β` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_beta_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J h β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ => partitionFunctionΛ G Λ ⟨J, h, β'⟩) β := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_beta_general_h
    (inducedGraph G Λ) J h β

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `J` at general
`h`**. -/
theorem partitionFunctionΛ_analyticAt_J_general_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β h J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ => partitionFunctionΛ G Λ ⟨J', h, β⟩) J := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_J_general_h
    (inducedGraph G Λ) β h J

/-- **Λ-layer: partitionFunction `AnalyticAt ℝ` in `h`**. -/
theorem partitionFunctionΛ_analyticAt_h
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β h : ℝ) :
    AnalyticAt ℝ (fun h' : ℝ => partitionFunctionΛ G Λ ⟨J, h', β⟩) h := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_analyticAt_h
    (inducedGraph G Λ) J β h

/-! ### §18.4-§18.6 capstones Λ-layer wraps -/

/-- **Λ-layer: §18.4 partitionFunction polymer-family form** capstone:
`Z_Λ(J, 0, β) = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_Γ ∏ tanh(β·J)^|P|`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_polymer_family
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_polymer_family
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.4 partitionFunction even-subgraph form** (FV (3.45))**:
`Z_Λ = 2^|Λ| · cosh(β·J)^|E_Λ| · ∑_X tanh(β·J)^|X|`. -/
theorem
partitionFunctionΛ_high_temp_expansion_h_zero_closed_evenSubgraphs
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) :
    partitionFunctionΛ G Λ ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ↑(Λ : Finset V) *
        Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card *
        ∑ X ∈ IsingModel.evenSubgraphs (inducedGraph G Λ),
          Real.tanh (β * J) ^ X.card := by
  simp only [partitionFunctionΛ_apply]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_closed_evenSubgraphs
    (inducedGraph G Λ) J β

/-- **Λ-layer: §18.6 freeEnergy decomposition** under `0 ≤ β·J` and
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy
    (inducedGraph G Λ) J β hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: §18.6 ferromagnetic freeEnergy decomposition** under
`0 ≤ J, 0 < β` and `Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_polymerFreeEnergy_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ =
      Real.log 2 +
        ((inducedGraph G Λ).edgeFinset.card : ℝ) /
            Fintype.card ↑(Λ : Finset V) *
          Real.log (Real.cosh (β * J)) +
        IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) /
            Fintype.card ↑(Λ : Finset V) :=
  IsingModel.freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    (inducedGraph G Λ) J β hJ hβ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: freeEnergy = log 2** at `β·J = 0`, under
`Λ.Nonempty`. -/
theorem freeEnergyΛ_eq_log_two_at_betaJ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : Λ.Nonempty) :
    freeEnergyΛ G Λ ⟨J, 0, β⟩ = Real.log 2 :=
  IsingModel.freeEnergy_eq_log_two_at_betaJ_zero
    (inducedGraph G Λ) hβJ (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Λ-layer: mayerPartialSum at N=1, t=1 = |allPolymers|**. -/
theorem mayerPartialSum_Λ_one_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 1 =
      (IsingModel.allPolymers (inducedGraph G Λ)).card :=
  IsingModel.mayerPartialSum_one_at_one (inducedGraph G Λ)

/-! ### §18.5 Mayer filter-connected + ε^n + mayerPartialSum
analyticOnNhd Λ-layer wraps -/

/-- **Λ-layer: mayerPartialSum `AnalyticOnNhd ℝ _ Set.univ`**. -/
theorem mayerPartialSum_Λ_analyticOnNhd
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    AnalyticOnNhd ℝ
      (fun s : ℝ => IsingModel.mayerPartialSum
          (inducedGraph G Λ) N s) Set.univ :=
  IsingModel.mayerPartialSum_analyticOnNhd (inducedGraph G Λ) N

/-- **Λ-layer: ε(t)^n as multi-Γ piFinset sum**. -/
theorem vdPolymerFamilies_sum_Λ_minus_one_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n =>
                (IsingModel.vdCompatiblePolymerFamilies
                  (inducedGraph G Λ)).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_minus_one_pow
    (inducedGraph G Λ) t n

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=0 = ∅**. -/
theorem mayerExpansionTerm_Λ_filter_connected_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  IsingModel.mayerExpansionTerm_filter_connected_zero
    (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm filter-connected at n=1 = full
piFinset**. -/
theorem mayerExpansionTerm_Λ_filter_connected_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers (inducedGraph G Λ)) :=
  IsingModel.mayerExpansionTerm_filter_connected_one (inducedGraph G Λ)

/-- **Λ-layer: filter-connected = filter-incompatible at n=2**. -/
theorem mayerExpansionTerm_Λ_two_filter_connected_eq_incompat
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (Fintype.piFinset
        (fun _ : Fin 2 =>
          IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      (Fintype.piFinset
          (fun _ : Fin 2 =>
            IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => IsingModel.PolymersIncompatible (ω 0) (ω 1)) :=
  IsingModel.mayerExpansionTerm_two_filter_connected_eq_incompat
    (inducedGraph G Λ)

end Ambient
end IsingModel
