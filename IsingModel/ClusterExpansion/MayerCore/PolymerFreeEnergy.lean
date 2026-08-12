import IsingModel.ClusterExpansion.MayerCore.ZeroBounds

/-!
# Cluster Expansion Polymer Free Energy Core

Mechanical child split from `ClusterExpansion/MayerCore.lean`.
-/

namespace IsingModel

open Finset

/-- **Polymer free energy** (Step 610): named wrapper for the LHS of
the Mayer expansion identity,
`polymerFreeEnergy G t := Real.log (∑_Γ ∏_{P ∈ Γ} t^|P|)`. The Mayer
identity then reads `polymerFreeEnergy G t = ∑_{n ≥ 0} mayerExpansionTerm G n t`
(general-`t` identity deferred). -/
noncomputable def polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) : ℝ :=
  Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)

/-- **`polymerFreeEnergy` at `t = 0`** (Step 610): equals `0` since
`vdPolymerFamilies_sum G 0 = 1`. -/
theorem polymerFreeEnergy_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 0 = 0 := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_zero, Real.log_one]

/-- **`polymerFreeEnergy` analyticAt for `t ≥ 0`** (Step 610): direct
restatement of Step 606 in the named-wrapper form. -/
theorem polymerFreeEnergy_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  log_vdPolymerFamilies_sum_analyticAt G ht

/-- **`polymerFreeEnergy` AnalyticOnNhd over `[0, ∞)`** (Step 610). -/
theorem polymerFreeEnergy_analyticOnNhd_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  log_vdPolymerFamilies_sum_analyticOnNhd_Ici_zero G

/-- **`polymerFreeEnergy` is `ContinuousAt` for `t ≥ 0`** (Step 611):
direct consequence of analyticAt. -/
theorem polymerFreeEnergy_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).continuousAt

/-- **`polymerFreeEnergy` is `DifferentiableAt` for `t ≥ 0`** (Step 611). -/
theorem polymerFreeEnergy_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => polymerFreeEnergy G s) t :=
  (polymerFreeEnergy_analyticAt G ht).differentiableAt

/-- **Mayer identity at `t = 0` in `polymerFreeEnergy` form** (Step 611):
restatement of Step 600 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    polymerFreeEnergy G 0 = mayerPartialSum G N 0 := by
  rw [polymerFreeEnergy_at_zero, mayerPartialSum_at_zero]

/-- **freeEnergy decomposition with `polymerFreeEnergy`** (Step 612):
under `0 < |ι|` and `0 ≤ β·J`,
  `f = log 2 + (|E|/|ι|) · log cosh(β·J) + polymerFreeEnergy G (tanh(β·J)) / |ι|`.
Restatement of `freeEnergy_high_temp_expansion_h_zero_closed` (Step 317)
using the polymer-family form (Step 547 bijection wraps the
`evenSubgraphs` sum into the `vdCompatiblePolymerFamilies` form). -/
theorem freeEnergy_eq_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι := by
  rw [freeEnergy_high_temp_expansion_h_zero_closed G J β hβJ hne]
  unfold polymerFreeEnergy
  rw [← evenSubgraphs_eq_inline_filter,
      evenSubgraphs_sum_eq_vdPolymerFamilies_sum G (Real.tanh (β * J))]

/-- **Ferromagnetic `freeEnergy = log 2 + ... + polymerFreeEnergy/|ι|`**
(Step 616): under `0 ≤ J`, `0 < β`, `0 < |ι|`, the Step 612 decomposition
holds (since `0 ≤ β·J` follows from `mul_nonneg`). -/
theorem freeEnergy_eq_polymerFreeEnergy_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) +
        polymerFreeEnergy G (Real.tanh (β * J)) / Fintype.card ι :=
  freeEnergy_eq_polymerFreeEnergy G J β (mul_nonneg hβ.le hJ) hne

/-- **Mayer identity at `β·J = 0` in `polymerFreeEnergy` form** (Step 617):
restate Step 609 using the named wrapper. -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  unfold polymerFreeEnergy
  exact mayer_identity_at_betaJ_zero G hβJ N

/-- **Mayer identity at `β = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_beta_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * J)) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * J)) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (zero_mul J) N

/-- **Mayer identity at `J = 0` in `polymerFreeEnergy` form** (Step 617). -/
theorem polymerFreeEnergy_eq_mayerPartialSum_at_J_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh (β * (0 : ℝ))) :=
  polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G (mul_zero β) N

/-- **`polymerFreeEnergy` analyticAt in `β`** (Step 613): named-wrapper
restatement of Step 608. -/
theorem polymerFreeEnergy_tanh_analyticAt_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) β :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_beta G J β hβJ

/-- **`polymerFreeEnergy` analyticAt in `J`** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticAt_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) J :=
  log_vdPolymerFamilies_sum_tanh_analyticAt_J G β J hβJ

/-- **`polymerFreeEnergy` AnalyticOnNhd in `β` over `[0, ∞)` (under
`0 ≤ J`)** (Step 613): for fixed `J ≥ 0`, the function is analytic at
every `β ≥ 0` since `0 ≤ β·J = β·J` follows from `mul_nonneg`. -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_beta_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ
      (fun β' : ℝ => polymerFreeEnergy G (Real.tanh (β' * J))) (Set.Ici 0) :=
  fun β hβ => polymerFreeEnergy_tanh_analyticAt_beta G J β (mul_nonneg hβ hJ)

/-- **`polymerFreeEnergy` AnalyticOnNhd in `J` over `[0, ∞)` (under
`0 ≤ β`)** (Step 613). -/
theorem polymerFreeEnergy_tanh_analyticOnNhd_J_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ
      (fun J' : ℝ => polymerFreeEnergy G (Real.tanh (β * J'))) (Set.Ici 0) :=
  fun J hJ => polymerFreeEnergy_tanh_analyticAt_J G β J (mul_nonneg hβ hJ)

/-- **`mayerPartialSum G 2 t` explicit formula** (Step 614):
`mayerPartialSum G 2 t = ∑_{P ∈ allPolymers G} t^|P|
                       - (1/2) ∑_{(P, Q) ∈ allPolymers², PolymersIncompatible P Q}
                          t^|P| · t^|Q|`.
The `N = 2` truncation of the Mayer expansion expressed entirely via
explicit polymer sums. Combines Step 592 (n=1: total polymer activity)
with Step 597 (n=2 filter form). -/
theorem mayerPartialSum_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    mayerPartialSum G 2 t =
      (∑ P ∈ allPolymers G, t ^ P.card) +
        (-1/2 : ℝ) *
          ∑ pq ∈ ((allPolymers G) ×ˢ (allPolymers G)).filter
              (fun pq => PolymersIncompatible pq.1 pq.2),
            (t ^ pq.1.card * t ^ pq.2.card) := by
  unfold mayerPartialSum
  rw [show ((2 : ℕ) + 1) = 3 from rfl,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      mayerExpansionTerm_zero, mayerExpansionTerm_one,
      mayerExpansionTerm_two_filter, zero_add]

/-- **Mayer identity for empty-polymer graphs** (Step 618): when
`allPolymers G = ∅`, `polymerFreeEnergy G t = mayerPartialSum G N t = 0`
for any `t` and `N`. The polymer-family sum reduces to the empty
family contributing 1, so `log 1 = 0`; on the Mayer side, for `n ≥ 1`
every entry `ω i` would have to be in `allPolymers G = ∅`, an empty
domain, so the piFinset is empty and the sum vanishes. -/
theorem mayer_identity_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t := by
  classical
  have h_vd : vdCompatiblePolymerFamilies G = {∅} := by
    apply Finset.ext
    intro Γ
    rw [mem_vdCompatiblePolymerFamilies, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨h_sub, _⟩
      rw [h_no, Finset.subset_empty] at h_sub
      exact h_sub
    · intro h_eq
      refine ⟨?_, ?_⟩
      · rw [h_eq, h_no]
      · rw [h_eq]
        exact IsCompatiblePolymerFamilyVertexDisjoint.empty G
  have h_lhs : polymerFreeEnergy G t = 0 := by
    unfold polymerFreeEnergy
    rw [h_vd, Finset.sum_singleton, Finset.prod_empty, Real.log_one]
  have h_rhs : mayerPartialSum G N t = 0 := by
    unfold mayerPartialSum
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rcases n with _ | k
    · exact mayerExpansionTerm_zero G t
    · unfold mayerExpansionTerm
      refine Finset.sum_eq_zero (fun ω hω => ?_)
      rw [Fintype.mem_piFinset] at hω
      have h0 : ω 0 ∈ allPolymers G := hω 0
      rw [h_no] at h0
      exact absurd h0 (Finset.notMem_empty _)
  rw [h_lhs, h_rhs]

/-- **Mayer identity tanh form for empty-polymer graphs** (Step 619):
restate Step 618 in `tanh(β·J)` form. -/
theorem mayer_identity_of_no_polymers_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers G h_no _ N

/-- **Mayer identity holds under disjunctive trivial conditions** (Step 651):
`polymerFreeEnergy G (tanh(β·J)) = mayerPartialSum G N (tanh(β·J))`
holds when either `β·J = 0` (so `tanh = 0`, both sides reduce to 0)
or `allPolymers G = ∅` (so both sides equal 0 via vanishing). -/
theorem mayer_identity_of_trivial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (h : β * J = 0 ∨ allPolymers G = ∅) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) := by
  rcases h with hβJ | hno
  · exact polymerFreeEnergy_eq_mayerPartialSum_at_betaJ_zero G hβJ N
  · exact mayer_identity_of_no_polymers_tanh G hno β J N

/-- **Mayer identity at `J = 0` and `β = 0`** (Step 653): both
specialisations bundled. -/
theorem mayer_identity_at_either_zero_polymer_free_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) :
    polymerFreeEnergy G (Real.tanh ((0 : ℝ) * (0 : ℝ))) =
      mayerPartialSum G N (Real.tanh ((0 : ℝ) * (0 : ℝ))) :=
  mayer_identity_of_trivial G (Or.inl (mul_zero 0)) N

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G t` under `t ≥ 0`**
(Step 654): trivially `mayerPartialSum G 0 t = 0` (Step 592) and
`0 ≤ polymerFreeEnergy G t` (via `Real.log_nonneg` + Step 605). -/
theorem mayerPartialSum_zero_le_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    mayerPartialSum G 0 t ≤ polymerFreeEnergy G t := by
  rw [mayerPartialSum_zero]
  unfold polymerFreeEnergy
  exact Real.log_nonneg (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G (tanh(β·J))` under
`0 ≤ β·J`** (Step 655). -/
theorem mayerPartialSum_zero_tanh_le_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    mayerPartialSum G 0 (Real.tanh (β * J)) ≤
      polymerFreeEnergy G (Real.tanh (β * J)) :=
  mayerPartialSum_zero_le_polymerFreeEnergy G (real_tanh_nonneg hβJ)

/-- **`mayerPartialSum G 0 ≤ polymerFreeEnergy G (tanh(β·J))`
ferromagnetic** (Step 656). -/
theorem mayerPartialSum_zero_tanh_le_polymerFreeEnergy_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    mayerPartialSum G 0 (Real.tanh (β * J)) ≤
      polymerFreeEnergy G (Real.tanh (β * J)) :=
  mayerPartialSum_zero_tanh_le_polymerFreeEnergy G (mul_nonneg hβ.le hJ)

/-- **`vdPolymerFamilies_sum` split as 1 + (Γ ≠ ∅) contribution**
(Step 657, Mayer general-t Phase A): writing
`vdSum G t = 1 + ε(t)` where `ε(t) = ∑_{Γ ∈ vdCompat, Γ ≠ ∅} ∏ t^|P|`.
Foundation for `log(1+ε)` Taylor expansion via Mayer combinatorics. -/
theorem vdPolymerFamilies_sum_eq_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdCompatiblePolymerFamilies G := by
    rw [mem_vdCompatiblePolymerFamilies]
    exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
  rw [show vdCompatiblePolymerFamilies G =
        insert (∅ : Finset (Finset (Sym2 ι)))
          ((vdCompatiblePolymerFamilies G).erase ∅) from
        (Finset.insert_erase h_empty_in).symm,
      Finset.sum_insert (Finset.notMem_erase _ _),
      Finset.prod_empty,
      Finset.erase_insert (Finset.notMem_erase _ _)]

/-- **`allPolymers G = ∅` when `G` has no edges** (Step 620): an
edgeless graph has no even subgraph other than `∅`, which is excluded
from `IsPolymer` by the non-emptiness clause. -/
theorem allPolymers_eq_empty_of_edgeFinset_empty
    {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) :
    allPolymers G = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_allPolymers] at hP
  -- IsPolymer G P ⇒ P ⊆ G.edgeFinset (= ∅) and P.Nonempty
  obtain ⟨e, heP⟩ := hP.nonempty
  have h_e : e ∈ G.edgeFinset := hP.isEven.subset heP
  rw [h_empty] at h_e
  exact absurd h_e (Finset.notMem_empty _)

/-- **Mayer identity for edgeless graphs** (Step 620): when
`G.edgeFinset = ∅`, the Mayer identity `polymerFreeEnergy G t =
mayerPartialSum G N t` holds for every `t` and `N`. Combines
Step 620's `allPolymers = ∅` with Step 618. -/
theorem mayer_identity_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    polymerFreeEnergy G t = mayerPartialSum G N t :=
  mayer_identity_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, `polymerFreeEnergy G t = 0` for every `t`,
since `vdCompatiblePolymerFamilies G = {∅}` and `log 1 = 0`. -/
theorem polymerFreeEnergy_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 := by
  rw [mayer_identity_of_no_polymers G h_no t 0, mayerPartialSum_zero]

/-- **`mayerPartialSum = 0` for empty-polymer graphs** (Step 621):
when `allPolymers G = ∅`, every Mayer term vanishes (no polymer
sequences exist for `n ≥ 1`; n=0 vanishes via Step 587). -/
theorem mayerPartialSum_eq_zero_of_no_polymers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_no : allPolymers G = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 := by
  rw [← mayer_identity_of_no_polymers G h_no t N,
      polymerFreeEnergy_eq_zero_of_no_polymers G h_no t]

/-- **Edgeless-graph Mayer identity in tanh form** (Step 622): lift
Step 620 to the `tanh(β·J)` argument. -/
theorem mayer_identity_of_edgeFinset_empty_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (β J : ℝ) (N : ℕ) :
    polymerFreeEnergy G (Real.tanh (β * J)) =
      mayerPartialSum G N (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty G h_empty _ N

/-- **`polymerFreeEnergy = 0` for edgeless graphs** (Step 623). -/
theorem polymerFreeEnergy_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) :
    polymerFreeEnergy G t = 0 :=
  polymerFreeEnergy_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t

/-- **`mayerPartialSum = 0` for edgeless graphs** (Step 623). -/
theorem mayerPartialSum_eq_zero_of_edgeFinset_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h_empty : G.edgeFinset = ∅) (t : ℝ) (N : ℕ) :
    mayerPartialSum G N t = 0 :=
  mayerPartialSum_eq_zero_of_no_polymers G
    (allPolymers_eq_empty_of_edgeFinset_empty G h_empty) t N

/-- **`polymerFreeEnergy` DifferentiableOn `[0, ∞)`** (Step 626):
lift Step 610's per-point AnalyticAt to DifferentiableOn over the
half-line. -/
theorem polymerFreeEnergy_differentiableOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    DifferentiableOn ℝ (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).differentiableAt).differentiableWithinAt

/-- **`polymerFreeEnergy` ContinuousOn `[0, ∞)`** (Step 627). -/
theorem polymerFreeEnergy_continuousOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ContinuousOn (fun s : ℝ => polymerFreeEnergy G s) (Set.Ici 0) :=
  fun _ ht =>
    ((polymerFreeEnergy_analyticAt G ht).continuousAt).continuousWithinAt

/-- **`mayerPartialSum` ContinuousOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_continuousOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_continuous G N).continuousOn

/-- **`mayerPartialSum` DifferentiableOn arbitrary set** (Step 628). -/
theorem mayerPartialSum_differentiableOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (s : Set ℝ) :
    DifferentiableOn ℝ (fun t : ℝ => mayerPartialSum G N t) s :=
  (mayerPartialSum_differentiable G N).differentiableOn

end IsingModel
