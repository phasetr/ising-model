import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy

/-!
# Cluster Expansion Polymer Free Energy Bounds

Mechanical child split from `ClusterExpansion/MayerCore.lean`.
-/

namespace IsingModel

open Finset

/-- **vdPolymerFamilies sum sandwich for `t ≥ 0`** (Step 631):
`1 ≤ vdSum G t ≤ (1+t)^|E|`. Combines Step 605 (≥ 1) with Step 629
(≤ (1+t)^|E|). -/
theorem vdPolymerFamilies_sum_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
  ⟨vdPolymerFamilies_sum_ge_one_of_nonneg G ht,
   vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht⟩

/-- **`polymerFreeEnergy ≤ |E| · log(1+t)` under `t ≥ 0`** (Step 630):
apply `Real.log_le_log` to Step 629's bound `vdSum ≤ (1+t)^|E|`. The
right-hand side `Real.log ((1+t)^|E|) = |E| · log(1+t)` via `Real.log_pow`. -/
theorem polymerFreeEnergy_le_card_log_one_plus_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) := by
  unfold polymerFreeEnergy
  have h_pos : 0 < ∑ Γ ∈ vdCompatiblePolymerFamilies G,
      ∏ P ∈ Γ, t ^ P.card :=
    vdPolymerFamilies_sum_pos_of_nonneg G ht
  have h_le : (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ G.edgeFinset.card :=
    vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht
  calc Real.log (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      ≤ Real.log ((1 + t) ^ G.edgeFinset.card) :=
            Real.log_le_log h_pos h_le
    _ = G.edgeFinset.card * Real.log (1 + t) := by
            rw [Real.log_pow]

/-- **`polymerFreeEnergy ≥ 0` under `t ≥ 0`** (Step 631): direct
consequence of Step 605 (`vdSum ≥ 1`) and `Real.log_nonneg`. -/
theorem polymerFreeEnergy_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t :=
  Real.log_nonneg (vdPolymerFamilies_sum_ge_one_of_nonneg G ht)

/-- **`polymerFreeEnergy` sandwich for `t ≥ 0`** (Step 631):
`0 ≤ polymerFreeEnergy G t ≤ |E| · log(1 + t)`. -/
theorem polymerFreeEnergy_sandwich_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polymerFreeEnergy G t ∧
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log (1 + t) :=
  ⟨polymerFreeEnergy_nonneg_of_nonneg G ht,
   polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht⟩

/-- **`polymerFreeEnergy` sandwich at `tanh(β·J)`** (Step 632): tanh-form
restatement of Step 631. Under `0 ≤ β·J`, `0 ≤ Real.tanh (β·J)`, so
the sandwich applies. -/
theorem polymerFreeEnergy_tanh_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_sandwich_of_nonneg G (real_tanh_nonneg hβJ)

/-- **`vdPolymerFamilies_sum` is monotone on `[0, ∞)`** (Step 633):
each term `t^|X|` is monotone in `t` for `t ≥ 0`, so the sum is too. -/
theorem vdPolymerFamilies_sum_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) := by
  intro t ht s hs hts
  refine Finset.sum_le_sum (fun Γ _ => ?_)
  refine Finset.prod_le_prod (fun P _ => pow_nonneg ht _) (fun P _ => ?_)
  exact pow_le_pow_left₀ ht hts _

/-- **`polymerFreeEnergy` is monotone on `[0, ∞)`** (Step 633): apply
`Real.log_le_log` to `vdSum` monotonicity. -/
theorem polymerFreeEnergy_monotoneOn_Ici_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    MonotoneOn (fun t : ℝ => polymerFreeEnergy G t) (Set.Ici 0) := by
  intro t ht s hs hts
  unfold polymerFreeEnergy
  exact Real.log_le_log (vdPolymerFamilies_sum_pos_of_nonneg G ht)
    (vdPolymerFamilies_sum_monotoneOn_Ici_zero G ht hs hts)

/-- The polymer free energy preserves order when the smaller activity is nonnegative. -/
theorem polymerFreeEnergy_le_of_le_of_nonneg_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    polymerFreeEnergy G t ≤ polymerFreeEnergy G s :=
  polymerFreeEnergy_monotoneOn_Ici_zero G ht (le_trans ht hts) hts

/-- **`polymerFreeEnergy ≤ |E| · t` under `t ≥ 0`** (Step 634):
sharpen Step 630 via `Real.log_le_sub_one_of_pos` (i.e. `log(1+t) ≤ t`). -/
theorem polymerFreeEnergy_le_card_mul_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * t := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h_pos : (0 : ℝ) < 1 + t := by linarith
  have := Real.log_le_sub_one_of_pos h_pos
  linarith

/-- **`polymerFreeEnergy ≤ |E|·tanh(β·J)` under `0 ≤ β·J`** (Step 635):
tanh form of Step 634. -/
theorem polymerFreeEnergy_tanh_le_card_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_le_card_mul_of_nonneg G (real_tanh_nonneg hβJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_sandwich`** (Step 636):
under `0 ≤ J, 0 < β`. -/
theorem polymerFreeEnergy_tanh_sandwich_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ polymerFreeEnergy G (Real.tanh (β * J)) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_tanh_sandwich G (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic `polymerFreeEnergy_tanh_le_card_mul`** (Step 636). -/
theorem polymerFreeEnergy_tanh_le_card_mul_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) :=
  polymerFreeEnergy_tanh_le_card_mul G (mul_nonneg hβ.le hJ)

/-- **`mayerExpansionTerm G 1 t ≥ 0` under `t ≥ 0`** (Step 637):
the n=1 Mayer term equals `∑_P t^|P|`, all non-negative. -/
theorem mayerExpansionTerm_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mayerExpansionTerm G 1 t := by
  rw [mayerExpansionTerm_one]
  exact Finset.sum_nonneg (fun P _ => pow_nonneg ht _)

/-- **`vdPolymerFamilies_sum` at `t = 1`** (Step 639): every product
`∏ 1^|P| = 1`, so the sum collapses to the cardinality of
`vdCompatiblePolymerFamilies G`. -/
theorem vdPolymerFamilies_sum_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (vdCompatiblePolymerFamilies G).card := by
  classical
  have h_each : ∀ Γ ∈ vdCompatiblePolymerFamilies G,
      (∏ P ∈ Γ, (1 : ℝ) ^ P.card) = 1 := by
    intro Γ _
    refine Finset.prod_eq_one (fun P _ => ?_)
    exact one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy` at `t = 1`** (Step 640): equals
`log |vdCompatiblePolymerFamilies G|`. Direct via Step 639. -/
theorem polymerFreeEnergy_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    polymerFreeEnergy G 1 =
      Real.log (vdCompatiblePolymerFamilies G).card := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_at_one]

/-- **`mayerPartialSum G 1 t = |allPolymers G|` at `t = 1`** (Step 641):
each polymer contributes `1^|P| = 1`, so the sum equals the number of
polymers. -/
theorem mayerPartialSum_one_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    mayerPartialSum G 1 1 = (allPolymers G).card := by
  classical
  rw [mayerPartialSum_one]
  have h_each : ∀ P ∈ allPolymers G, (1 : ℝ) ^ P.card = 1 := fun _ _ => one_pow _
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **`polymerFreeEnergy ≤ |E| · log 2` for `0 ≤ t ≤ 1`** (Step 642):
under `t ≤ 1`, `log(1+t) ≤ log 2`. -/
theorem polymerFreeEnergy_le_card_log_two_of_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    polymerFreeEnergy G t ≤ G.edgeFinset.card * Real.log 2 := by
  refine (polymerFreeEnergy_le_card_log_one_plus_of_nonneg G ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Real.log_le_log (by linarith) (by linarith)

/-- **`polymerFreeEnergy_tanh ≤ |E| · log 2` under `0 ≤ β·J`** (Step 643):
since `tanh(β·J) < 1` always, Step 642 applies. -/
theorem polymerFreeEnergy_tanh_le_card_log_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_le_card_log_two_of_le_one G (real_tanh_nonneg hβJ)
    (Real.tanh_lt_one _).le

/-- **Ferromagnetic `polymerFreeEnergy_tanh ≤ |E| · log 2`** (Step 644). -/
theorem polymerFreeEnergy_tanh_le_card_log_two_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ}
    (hJ : 0 ≤ J) (hβ : 0 < β) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  polymerFreeEnergy_tanh_le_card_log_two G (mul_nonneg hβ.le hJ)

/-- **`polymerFreeEnergy_tanh` double bound** (Step 645): under
`0 ≤ β·J`, both `polymerFreeEnergy_tanh ≤ |E|·tanh(β·J)` (Step 635)
and `≤ |E|·log 2` (Step 643) hold simultaneously. -/
theorem polymerFreeEnergy_tanh_double_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J) :
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.tanh (β * J) ∧
    polymerFreeEnergy G (Real.tanh (β * J)) ≤
      G.edgeFinset.card * Real.log 2 :=
  ⟨polymerFreeEnergy_tanh_le_card_mul G hβJ,
   polymerFreeEnergy_tanh_le_card_log_two G hβJ⟩

/-- **`mayerPartialSum` recurrence in `N`** (Step 638):
`mayerPartialSum G (N+1) t = mayerPartialSum G N t + mayerExpansionTerm G (N+1) t`. -/
theorem mayerPartialSum_succ
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerPartialSum G (N + 1) t =
      mayerPartialSum G N t + mayerExpansionTerm G (N + 1) t := by
  unfold mayerPartialSum
  rw [show ((N + 1) + 1) = (N + 1) + 1 from rfl, Finset.sum_range_succ]

/-- **`mayerExpansionTerm = mayerPartialSum` diff** (Step 646):
rearrangement of Step 638. -/
theorem mayerExpansionTerm_eq_mayerPartialSum_diff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (N : ℕ) (t : ℝ) :
    mayerExpansionTerm G (N + 1) t =
      mayerPartialSum G (N + 1) t - mayerPartialSum G N t := by
  rw [mayerPartialSum_succ]
  ring

/-- **`mayerExpansionTerm G 2 t ≤ 0` under `t ≥ 0`** (Step 637):
the n=2 Mayer term equals `-1/2 · ∑_{(P,Q) incompat} t^|P|·t^|Q|`,
non-positive. Matches the alternating sign of log(1+x) Taylor
coefficients. -/
theorem mayerExpansionTerm_two_nonpos_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    mayerExpansionTerm G 2 t ≤ 0 := by
  rw [mayerExpansionTerm_two_filter]
  refine mul_nonpos_of_nonpos_of_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg (fun pq _ => ?_)
  exact mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)

/-- **`polymerFreeEnergy` HasDerivAt** (Step 625): explicit derivative
of `polymerFreeEnergy G t = Real.log (vdPolymerFamilies_sum G t)` via
the log-derivative formula `(log f)' = f' / f`. The derivative of
`vdPolymerFamilies_sum G` is given by Step 575 (explicit polynomial
form), and positivity (Step 605) ensures `f t ≠ 0`. -/
theorem polymerFreeEnergy_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => polymerFreeEnergy G s)
      ((∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)) t := by
  unfold polymerFreeEnergy
  exact (vdPolymerFamilies_sum_hasDerivAt G t).log
    (vdPolymerFamilies_sum_pos_of_nonneg G ht).ne'

/-- **`freeEnergy = log 2` at `β·J = 0`** (Step 624): when `β·J = 0`,
the Step 612 decomposition reduces to `f = log 2` since
`cosh(0) = 1`, `log 1 = 0`, and `polymerFreeEnergy G (tanh 0) = 0`
(Step 600). Recovers the well-known free-energy value at trivial
slices. -/
theorem freeEnergy_eq_log_two_at_betaJ_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : β * J = 0) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ = Real.log 2 := by
  rw [freeEnergy_eq_polymerFreeEnergy G J β (hβJ.symm ▸ le_refl 0) hne, hβJ,
      Real.cosh_zero, Real.log_one, Real.tanh_zero,
      polymerFreeEnergy_at_zero, mul_zero, zero_div, add_zero, add_zero]

end IsingModel
