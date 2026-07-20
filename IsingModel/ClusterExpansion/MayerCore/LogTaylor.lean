import IsingModel.ClusterExpansion.MayerCore.PolymerBounds

/-!
# Cluster Expansion Mayer Log Taylor

Mechanical child split from `ClusterExpansion/MayerCore.lean`.
-/

namespace IsingModel

open Finset

/-- **`polymerFreeEnergy = log(1 + ε)` form** (Step 658, Mayer
general-t Phase A): rewrite `polymerFreeEnergy G t` as
`Real.log (1 + ε(t))` where `ε(t) = ∑_{Γ ≠ ∅} ∏ t^|P|`. Foundation
for Taylor expansion `log(1+ε) = ∑_n (-1)^(n-1)/n · ε^n` for `|ε| < 1`. -/
theorem polymerFreeEnergy_eq_log_one_add_eps
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    polymerFreeEnergy G t =
      Real.log (1 + ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) := by
  unfold polymerFreeEnergy
  rw [vdPolymerFamilies_sum_eq_one_add]

/-- **`ε(0) = 0`** (Step 659, Mayer general-t Phase A): every Γ ≠ ∅
in `vdCompatiblePolymerFamilies` contains a polymer P with |P| ≥ 1,
so 0^|P| = 0 and the product vanishes. -/
theorem vdPolymerFamilies_sum_minus_one_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
  rw [Finset.mem_erase] at hΓ
  obtain ⟨h_ne, h_in⟩ := hΓ
  obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
  rw [mem_vdCompatiblePolymerFamilies] at h_in
  have hP_polymer : IsPolymer G P := mem_allPolymers.mp (h_in.1 hP)
  have hP_pos : 0 < P.card := hP_polymer.nonempty.card_pos
  exact Finset.prod_eq_zero hP (zero_pow hP_pos.ne')

/-- **`ε(t) ≥ 0` for `t ≥ 0`** (Step 660, Mayer general-t Phase A):
each summand is a finite product of non-negative terms `t^|P|`. -/
theorem vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card := by
  refine Finset.sum_nonneg (fun _ _ => ?_)
  exact Finset.prod_nonneg (fun _ _ => pow_nonneg ht _)

/-- **`ε(t) ≤ (1+t)^|E| - 1` for `t ≥ 0`** (Step 661, Mayer general-t
Phase A): subtract 1 from Step 629's `vdSum ≤ (1+t)^|E|` after using
the Step 657 split. -/
theorem vdPolymerFamilies_sum_minus_one_le_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) ≤ (1 + t) ^ G.edgeFinset.card - 1 := by
  have h_le := vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg G ht
  rw [vdPolymerFamilies_sum_eq_one_add] at h_le
  linarith

/-- **`ε(t)` is continuous** (Step 662, Mayer general-t Phase A):
finite sum of finite products of monomials in `t`. -/
theorem vdPolymerFamilies_sum_minus_one_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ (fun Γ _ => ?_)
  refine continuous_finset_prod _ (fun P _ => ?_)
  exact continuous_id.pow _

/-- **`ε(t)` is analyticAt every `t`** (Step 663, Mayer general-t
Phase A): finite sum of analytic terms via `analyticAt_prod_pow`. -/
theorem vdPolymerFamilies_sum_minus_one_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, s ^ P.card) t := by
  refine Finset.analyticAt_fun_sum _ (fun Γ _ => analyticAt_prod_pow Γ t)

/-- **`ε(t) → 0` as `t → 0`** (Step 664, Mayer general-t Phase A):
combine continuity (Step 662) with `ε(0) = 0` (Step 659) to get
the limit at `t = 0`. -/
theorem vdPolymerFamilies_sum_minus_one_tendsto_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Filter.Tendsto (fun t : ℝ =>
      ∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) (nhds 0) (nhds 0) := by
  have h_cont := (vdPolymerFamilies_sum_minus_one_continuous G).continuousAt (x := 0)
  rw [ContinuousAt, vdPolymerFamilies_sum_minus_one_at_zero] at h_cont
  exact h_cont

/-- **`ε(t) < 1` eventually as `t → 0`** (Step 665, Mayer general-t
Phase A): since ε is continuous and ε(0) = 0, in some nbhd of 0,
ε(t) < 1 (the threshold for `log(1+ε)` Taylor convergence). -/
theorem vdPolymerFamilies_sum_minus_one_lt_one_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) < 1 := by
  exact (vdPolymerFamilies_sum_minus_one_tendsto_zero G).eventually_lt_const zero_lt_one

/-- **ε(t)^n at t=0 for n ≥ 1** (Step 668, Mayer general-t Phase A):
since `ε(0) = 0` and `0^n = 0` for `n ≥ 1`, every `n`-th power
vanishes at t=0. -/
theorem vdPolymerFamilies_sum_minus_one_pow_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 := by
  rw [vdPolymerFamilies_sum_minus_one_at_zero]
  exact zero_pow (by omega : n ≠ 0)

/-- **ε(t)^n expansion as sum over Γ-tuples** (Step 667, Mayer
general-t Phase A): apply `Finset.sum_pow'` to express
  ε(t)^n = ∑_{(Γ_1, ..., Γ_n) ∈ piFinset (vdCompat.erase ∅)^n}
            ∏_i ∏_{P ∈ Γ_i} t^|P|.
This is the multi-Γ-tuple expansion needed to combine with
log(1+x) Taylor series (Step 666). -/
theorem vdPolymerFamilies_sum_minus_one_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => (vdCompatiblePolymerFamilies G).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, t ^ P.card :=
  Finset.sum_pow' _ _ n

/-- **`Real.log(1+x)` power series for `|x| < 1`** (Step 666, Mayer
general-t Phase A): wrapper of Mathlib's `hasSum_pow_div_log_of_abs_lt_one`
applied at `-x`, giving
  HasSum (fun n => (-1)^n · x^(n+1) / (n+1)) (Real.log (1 + x))

This is the standard alternating-sign log(1+x) Taylor series, which
matches the n-th order Mayer-expansion contribution structure. -/
theorem hasSum_real_log_one_add_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1))
      (Real.log (1 + x)) := by
  have h_neg : |(-x)| < 1 := by rwa [abs_neg]
  have h_base : HasSum (fun n : ℕ => (-x) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - -x)) := Real.hasSum_pow_div_log_of_abs_lt_one h_neg
  rw [show ((1 : ℝ) - -x) = 1 + x from by ring] at h_base
  have h' := h_base.neg
  rw [neg_neg] at h'
  convert h' using 1
  funext n
  have h_neg_pow : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by
    rw [pow_succ]; ring
  rw [show ((-x : ℝ) ^ (n + 1)) = (-1) ^ (n + 1) * x ^ (n + 1) from by ring,
      h_neg_pow]
  ring

/-- **polymerFreeEnergy power series via log(1+ε) Taylor**: when
`|ε(t)| < 1`, the polymer free energy admits a convergent series
representation
  polymerFreeEnergy G t = ∑_{n ≥ 0} (-1)^n · ε(t)^(n+1) / (n+1)
where `ε(t) = ∑_{Γ ≠ ∅} ∏ t^|P|`. This connects Mayer-side
combinatorial sums to the analytic log Taylor series.

Bundles together the ε-power expansion (Step 667), log(1+x) Taylor
(Step 666), and `polymerFreeEnergy = log(1+ε)` (Step 658). The full
Mayer identity (matching this sum to a polymer-sequence sum via
Mayer combinatorial identity for `K_n` connected subgraphs)
remains deferred; this lemma provides the analytic side. -/
theorem polymerFreeEnergy_hasSum_via_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
                       ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G t) := by
  rw [polymerFreeEnergy_eq_log_one_add_eps]
  exact hasSum_real_log_one_add_of_abs_lt_one h_abs

/-- **polymerFreeEnergy series convergence eventually** (companion
bundle): in some neighbourhood of `t = 0`, the convergent log(1+ε)
representation holds. -/
theorem polymerFreeEnergy_hasSum_via_log_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
            (n + 1))
        (polymerFreeEnergy G t) := by
  have h_abs_tendsto :
      Filter.Tendsto (fun t : ℝ =>
        |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, t ^ P.card|) (nhds 0) (nhds 0) := by
    have h := vdPolymerFamilies_sum_minus_one_tendsto_zero G
    simpa using (Continuous.tendsto continuous_abs (0 : ℝ)).comp h
  have h_abs_lt : ∀ᶠ t : ℝ in nhds 0,
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card| < 1 :=
    h_abs_tendsto.eventually_lt_const zero_lt_one
  exact h_abs_lt.mono (fun t h => polymerFreeEnergy_hasSum_via_log G h)

/-- **Explicit convergence radius for Mayer log expansion**: under
`0 ≤ t` with `(1 + t) ^ |E(G)| < 2`, the polymer free energy admits
the convergent series representation
  polymerFreeEnergy G t = ∑_{n ≥ 0} (-1)^n · ε(t)^(n+1) / (n+1).

Combines Step 661 (`ε(t) ≤ (1+t)^|E| - 1`) and Step 660 (`ε(t) ≥ 0`)
to derive `|ε(t)| < 1`, then applies `polymerFreeEnergy_hasSum_via_log`. -/
theorem polymerFreeEnergy_hasSum_via_log_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (h_pow : (1 + t) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G t) := by
  have h_eps_nonneg := vdPolymerFamilies_sum_minus_one_nonneg_of_nonneg G ht
  have h_eps_le := vdPolymerFamilies_sum_minus_one_le_of_nonneg G ht
  have h_eps_lt_one :
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, t ^ P.card| < 1 := by
    rw [abs_of_nonneg h_eps_nonneg]
    linarith
  exact polymerFreeEnergy_hasSum_via_log G h_eps_lt_one

/-- **`polymerFreeEnergy` log-Taylor expansion (tanh form)** (§18.5
GJ-proposition-bundle): tanh-substituted version of
`polymerFreeEnergy_hasSum_via_log_of_pow_lt_two` for the
ferromagnetic Ising activity `t = tanh(β·J)` under `0 ≤ β·J` and
`(1 + tanh(β·J))^|E| < 2`. -/
theorem polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G (Real.tanh (β * J))) :=
  polymerFreeEnergy_hasSum_via_log_of_pow_lt_two G
    (real_tanh_nonneg hβJ) h_pow

/-- **`polymerFreeEnergy` log-Taylor expansion (ferromagnetic tanh
form)** (§18.5 ferromagnetic): under `0 ≤ J, 0 < β` and
`(1 + tanh(β·J))^|E| < 2`, same `HasSum` log-Taylor expansion. -/
theorem polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^ G.edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (polymerFreeEnergy G (Real.tanh (β * J))) :=
  polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two G
    (mul_nonneg hβ.le hJ) h_pow


end IsingModel
