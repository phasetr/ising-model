import IsingModel.ClusterExpansion.AnchoredComponentRatio
import IsingModel.ClusterExpansion.AvoidingRatioExp
import IsingModel.ClusterExpansion.TwoPointCorrelationHTBound

/-!
# General-boundary volume-uniform correlation-ratio bound (GJ Theorem 17.6.1, §18)

This file is **brick K3** — the crux — of the project-specific lattice-Ising general-source
(`Q_A`) ratio-bound chain (issue #4404), architecturally analogous to the cluster-expansion method
of Glimm–Jaffe Chapter 18 but not literal coverage of Glimm–Jaffe Theorem 17.6.1.
It upgrades the two-point (pair) capstone
`correlationComplex_two_point_norm_le_of_high_temp` (`TwoPointCorrelationHTBound.lean`) to a
volume-uniform norm bound on the *general-boundary* correlation ratio `Q_A / Q_∅` for an arbitrary
boundary set `A`, on the convergent high-temperature Kotecký–Preiss (KP) activity window.

The proof is the **strong induction on `|A|`**, quantified over *all* graphs `G` with
`G.maxDegree ≤ Δ` (the recursion re-enters at the delete-edges graph `Gavoid G C`, a different
graph on the same vertex type), that discharges the per-component hypothesis of the K2 packaging
term by term.  It consumes K1 (`htSubgraphSum_anchored_peel`, `AnchoredPeel.lean`) and K2
(`AnchoredComponentRatio.lean`), and reuses the pair-leaf avoiding-ratio machinery
(`AvoidingRatioExp.lean`, `MayerSumDiffSupportBoundComplex.lean`) verbatim.

The bound function `generalRatioBoundFun Δ : ℕ → ℝ` is an explicit finite nonnegative recursion; it
is **volume-uniform** (independent of the vertex type, the graph, the exhaustion stage, and the
actual `G.maxDegree`) but blows up combinatorially in `|A|`.  This is harmless: GJ Theorem 17.6.1
fixes the observable `Sₙ`, hence fixes `A`, and only volume-uniformity is needed downstream.

Scope: this is the convergent **high-temperature (KP) window** content — GJ's "`σ` large ⇒
convergent cluster expansions (cf. Chapter 18)".  It is *not* the `σ_c < σ` / Ornstein–Zernike /
§18-analyticity content of issue #4386 (which needs uniform control of the true rate down to
criticality).

References: Glimm–Jaffe, *Quantum Physics* (2nd ed., Springer, 1987), Theorem 17.6.1 (p.313),
§17.5–17.6 (pp.311–314), Chapter 18 cluster expansion (§18.4–18.7, high-temperature KP window);
Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (CUP, 2017), §3.7.3.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### K3a — the explicit bound function and its closing inequality -/

/-- The strong-recursion step of `generalRatioBoundFun` (K3a).  On the successor `m + 1` it returns
`twoPointHTBoundValue Δ · ∑_{j ≤ m} (m choose j) · (previous value at j)`; on `0` it returns `1`.
The `Finset.range (m + 1) |>.attach` reindexing exposes the `j < m + 1` membership proof needed to
call the strong-recursion argument `ih`. -/
private noncomputable def generalRatioBoundFunStep (Δ : ℕ) : ∀ n : ℕ, (∀ m : ℕ, m < n → ℝ) → ℝ
  | 0, _ => 1
  | (m + 1), ih =>
      twoPointHTBoundValue Δ *
        ∑ j ∈ (Finset.range (m + 1)).attach,
          (m.choose j.1 : ℝ) * ih j.1 (Finset.mem_range.mp j.2)

/-- **The general-ratio bound function** `𝐌_Δ : ℕ → ℝ` (K3a).  Defined by strong recursion with
`𝐌_Δ 0 = 1` and, for `k ≥ 1`, `𝐌_Δ k = twoPointHTBoundValue Δ · ∑_{j=0}^{k-1} (k-1 choose j) 𝐌_Δ j`.
It is graph-free, nonnegative and finite; it dominates the Wick / double-factorial pairing count
that GJ p.313 predicts for "sums of products of two-point functions", and blows up in `k` (which is
harmless, since the observable fixes `|A|`). -/
noncomputable def generalRatioBoundFun (Δ k : ℕ) : ℝ :=
  Nat.strongRecOn' k (generalRatioBoundFunStep Δ)

/-- Strong-recursion unfolding of `generalRatioBoundFun` into its step. -/
theorem generalRatioBoundFun_eq (Δ k : ℕ) :
    generalRatioBoundFun Δ k
      = generalRatioBoundFunStep Δ k (fun m _ => generalRatioBoundFun Δ m) :=
  Nat.strongRecOn'_beta

/-- Base value `𝐌_Δ 0 = 1`. -/
theorem generalRatioBoundFun_zero (Δ : ℕ) : generalRatioBoundFun Δ 0 = 1 :=
  generalRatioBoundFun_eq Δ 0

/-- Successor recursion
`𝐌_Δ (m+1) = twoPointHTBoundValue Δ · ∑_{j=0}^{m} (m choose j) 𝐌_Δ j`. -/
theorem generalRatioBoundFun_succ (Δ m : ℕ) :
    generalRatioBoundFun Δ (m + 1)
      = twoPointHTBoundValue Δ *
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * generalRatioBoundFun Δ j := by
  rw [generalRatioBoundFun_eq]
  simp only [generalRatioBoundFunStep]
  rw [Finset.sum_attach (Finset.range (m + 1))
    (fun j => (m.choose j : ℝ) * generalRatioBoundFun Δ j)]

/-- The bound function is nonnegative. -/
theorem generalRatioBoundFun_nonneg (Δ k : ℕ) : 0 ≤ generalRatioBoundFun Δ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | m
    · rw [generalRatioBoundFun_zero]; norm_num
    · rw [generalRatioBoundFun_succ]
      refine mul_nonneg (le_of_lt (twoPointHTBoundValue_pos Δ)) (Finset.sum_nonneg ?_)
      intro j hj
      exact mul_nonneg (by positivity) (ih j (Finset.mem_range.mp hj))

omit [Fintype ι] in
/-- **K3a — the closing inequality.**  Summing the per-block value
`twoPointHTBoundValue Δ · 𝐌_Δ |A ∖ B|` over the peel index set `evenSubsetsThrough A a₀` is bounded
by `𝐌_Δ |A|`.  The index set embeds into `{B : a₀ ∈ B ⊆ A}` (dropping the evenness constraint, which
`𝐌_Δ ≥ 0` allows); the involution `B ↦ A ∖ B` maps it onto the powerset of `A ∖ {a₀}`, and grouping
by cardinality with `Finset.card_powersetCard` yields the `(|A|-1 choose j)` binomial recursion of
`generalRatioBoundFun_succ`. -/
theorem generalRatioBoundFun_closing (Δ : ℕ) {A : Finset ι} {a₀ : ι} (ha₀ : a₀ ∈ A) :
    ∑ B ∈ evenSubsetsThrough A a₀,
        twoPointHTBoundValue Δ * generalRatioBoundFun Δ (A \ B).card
      ≤ generalRatioBoundFun Δ A.card := by
  classical
  have hκ : 0 ≤ twoPointHTBoundValue Δ := le_of_lt (twoPointHTBoundValue_pos Δ)
  obtain ⟨m, hm⟩ : ∃ m, A.card = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr ⟨a₀, ha₀⟩).ne'
  set S : Finset (Finset ι) := A.powerset.filter (fun B => a₀ ∈ B) with hS
  have hsub : evenSubsetsThrough A a₀ ⊆ S := by
    intro B hB
    rw [evenSubsetsThrough, Finset.mem_filter, Finset.mem_powerset] at hB
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hB.1, hB.2.1⟩
  have hcardm : (A \ {a₀}).card = m := by
    rw [← Finset.erase_eq, Finset.card_erase_of_mem ha₀, hm, Nat.add_sub_cancel]
  have hstep2 : ∑ B ∈ S, generalRatioBoundFun Δ (A \ B).card
      = ∑ D ∈ (A \ {a₀}).powerset, generalRatioBoundFun Δ D.card := by
    refine Finset.sum_nbij' (fun B => A \ B) (fun D => A \ D) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      rw [hS, Finset.mem_filter, Finset.mem_powerset] at hB
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨hx.1, ?_⟩
      rintro rfl
      exact hx.2 hB.2
    · intro D hD
      rw [Finset.mem_powerset] at hD
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.mem_sdiff]
      refine ⟨ha₀, ?_⟩
      intro ha₀D
      have h := hD ha₀D
      rw [Finset.mem_sdiff, Finset.mem_singleton] at h
      exact h.2 rfl
    · intro B hB
      rw [hS, Finset.mem_filter, Finset.mem_powerset] at hB
      exact Finset.sdiff_sdiff_eq_self hB.1
    · intro D hD
      rw [Finset.mem_powerset] at hD
      exact Finset.sdiff_sdiff_eq_self (hD.trans Finset.sdiff_subset)
    · intro B _; rfl
  have hstep3 : ∑ D ∈ (A \ {a₀}).powerset, generalRatioBoundFun Δ D.card
      = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * generalRatioBoundFun Δ j := by
    rw [Finset.sum_powerset, hcardm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_powersetCard, hcardm, nsmul_eq_mul]
  calc ∑ B ∈ evenSubsetsThrough A a₀,
          twoPointHTBoundValue Δ * generalRatioBoundFun Δ (A \ B).card
      = twoPointHTBoundValue Δ *
          ∑ B ∈ evenSubsetsThrough A a₀, generalRatioBoundFun Δ (A \ B).card := by
        rw [Finset.mul_sum]
    _ ≤ twoPointHTBoundValue Δ * ∑ B ∈ S, generalRatioBoundFun Δ (A \ B).card := by
        refine mul_le_mul_of_nonneg_left ?_ hκ
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun B _ _ => generalRatioBoundFun_nonneg Δ _)
    _ = twoPointHTBoundValue Δ *
          ∑ D ∈ (A \ {a₀}).powerset, generalRatioBoundFun Δ D.card := by rw [hstep2]
    _ = twoPointHTBoundValue Δ *
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * generalRatioBoundFun Δ j := by
        rw [hstep3]
    _ = generalRatioBoundFun Δ (m + 1) := (generalRatioBoundFun_succ Δ m).symm
    _ = generalRatioBoundFun Δ A.card := by rw [hm]

/-! ### K3b — the per-component analytic core -/

/-- **K3b — per-component avoiding-ratio discharge** (the analytic crux).  Given the
induction-on-`Gavoid` bound `hIH` on the ratio `Q_{A'}(Gavoid G C)/Q_∅(Gavoid G C) ≤ Msub`, the
per-component avoiding remainder over the fixed denominator `Q_∅(G)` obeys the geometric-series
shape `‖t‖^{|C|} · ‖Q^{av}_{C,A'}(G)/Q_∅(G)‖ ≤ (Msub · e⁸) · (R · e⁸)^{|C|}` consumed by K2c.  The
two crux resolutions are settled here: (a) Gavoid-uniformity — every window constant is keyed to
`R` (from the uniform cap `Δ`), so it survives `Gavoid G C`; (b) the cross-level denominator
bookkeeping — the provably-nonzero intermediate `Q_∅(Gavoid G C) = exp(…) ≠ 0` splits the target
ratio into the IH times the pair-leaf avoiding ratio `Q_∅(Gavoid G C)/Q_∅(G) ≤ e^{8(|C|+1)}`.  This
reuses the pair-leaf calc of `correlationComplex_two_point_norm_le_of_high_temp` verbatim, with
`Msub` threaded in. -/
theorem perComponent_avoiding'_ratio_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) (A' : Finset ι) {t : ℂ} {R : ℝ} (hRpos : 0 < R)
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkpt64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 64)
    (htz : t ∈ Metric.ball (0 : ℂ) R)
    (hCsub : C ⊆ G.edgeFinset) (hCne : C.Nonempty) (hCconn : IsEdgeConnected C)
    (Msub : ℝ) (hMsub : 0 ≤ Msub)
    (hIH : ‖htSubgraphSum (Gavoid G C) A' t / htSubgraphSum (Gavoid G C) (∅ : Finset ι) t‖
        ≤ Msub) :
    ‖t‖ ^ C.card
        * ‖htSubgraphSumAvoiding' G C A' t / htSubgraphSum G (∅ : Finset ι) t‖
      ≤ (Msub * Real.exp 8) * (R * Real.exp 8) ^ C.card := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have htRlt : ‖t‖ < R := by
    have h := htz; rw [Metric.mem_ball, dist_zero_right] at h; exact h
  have htRle : ‖t‖ ≤ R := le_of_lt htRlt
  have httG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 6 := by linarith [hkpt64]
  obtain ⟨hkpt, hρt⟩ := kp_tail_conditions_of_lt httG6
  -- the two nonvanishing empty-boundary partitions
  obtain ⟨hkpAvoid, hρAvoid⟩ := gavoid_kp_conditions (G := G) (C := C) hkpR hρR
  have hQ0Gav : htSubgraphSum (Gavoid G C) (∅ : Finset ι) t
      = Complex.exp (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t) :=
    htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex (Gavoid G C) hRpos hkpAvoid hρAvoid
      htz
  have hQ0Gavne : htSubgraphSum (Gavoid G C) (∅ : Finset ι) t ≠ 0 := by
    rw [hQ0Gav]; exact Complex.exp_ne_zero _
  -- the pair-leaf avoiding ratio `Q_∅(Gavoid G C)/Q_∅(G) ≤ e^{8(|C|+1)}`
  have hleafeq : htSubgraphSum (Gavoid G C) (∅ : Finset ι) t = htSubgraphSumAvoiding G C t :=
    (htSubgraphSumAvoiding_eq_htSubgraphSum_empty_Gavoid G C t).symm
  have hratio :=
    norm_htSubgraphSumAvoiding_div_htSubgraphSum_empty_le (G := G) (C := C) (R := R)
      hRpos hkpR hρR htz
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) with hrrdef
  set κ : ℝ := (1 / (1 - rr)) * (1 - 4 * rr / (1 - rr) ^ 2)⁻¹ ^ 2 with hκdef
  have hrr_nonneg : 0 ≤ rr := by positivity
  have hκle : κ ≤ 8 := by
    simpa [κ, rr] using kpCoeff_le_eight hrr_nonneg (by simpa [rr] using hkpt64)
  have hdiff :=
    norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card_complex
      (G := G) (C := C) (z := t) hkpt hρt
  have hdiff8 :
      ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
          - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
        ≤ 8 * ((polymerSupport C).card : ℝ) := by
    calc
      ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
          - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖
        ≤ κ * ((polymerSupport C).card : ℝ) := by simpa [κ, rr] using hdiff
      _ ≤ 8 * ((polymerSupport C).card : ℝ) :=
          mul_le_mul_of_nonneg_right hκle (by positivity)
  have hsupp_nat : (polymerSupport C).card ≤ C.card + 1 :=
    polymerSupport_card_le_card_add_one_of_isEdgeConnected G hCsub hCne hCconn
  have hsupp_real : ((polymerSupport C).card : ℝ) ≤ (C.card : ℝ) + 1 := by exact_mod_cast hsupp_nat
  have hleaf : ‖htSubgraphSum (Gavoid G C) (∅ : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖
      ≤ Real.exp (8 * ((C.card : ℝ) + 1)) := by
    rw [hleafeq]
    calc
      ‖htSubgraphSumAvoiding G C t / htSubgraphSum G (∅ : Finset ι) t‖
        ≤ Real.exp ‖(∑' n : ℕ, mayerExpansionTermComplex G n t)
            - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n t)‖ := hratio
      _ ≤ Real.exp (8 * ((polymerSupport C).card : ℝ)) := Real.exp_le_exp.mpr hdiff8
      _ ≤ Real.exp (8 * ((C.card : ℝ) + 1)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsupp_real (by norm_num))
  -- assemble
  have htpow : ‖t‖ ^ C.card ≤ R ^ C.card :=
    pow_le_pow_left₀ (norm_nonneg t) htRle C.card
  have hnorm_eq :
      ‖htSubgraphSum (Gavoid G C) A' t / htSubgraphSum G (∅ : Finset ι) t‖
        = ‖htSubgraphSum (Gavoid G C) A' t / htSubgraphSum (Gavoid G C) (∅ : Finset ι) t‖
          * ‖htSubgraphSum (Gavoid G C) (∅ : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖ := by
    rw [← norm_mul, div_mul_div_cancel₀ hQ0Gavne]
  rw [htSubgraphSumAvoiding'_eq_htSubgraphSum_Gavoid G C A' t, hnorm_eq]
  calc
    ‖t‖ ^ C.card
        * (‖htSubgraphSum (Gavoid G C) A' t / htSubgraphSum (Gavoid G C) (∅ : Finset ι) t‖
           * ‖htSubgraphSum (Gavoid G C) (∅ : Finset ι) t / htSubgraphSum G (∅ : Finset ι) t‖)
      ≤ R ^ C.card * (Msub * Real.exp (8 * ((C.card : ℝ) + 1))) := by
        exact mul_le_mul htpow (mul_le_mul hIH hleaf (norm_nonneg _) hMsub) (by positivity)
          (pow_nonneg hRnonneg _)
    _ = (Msub * Real.exp 8) * (R * Real.exp 8) ^ C.card := by
        rw [show R ^ C.card * (Msub * Real.exp (8 * ((C.card : ℝ) + 1)))
              = Msub * (R ^ C.card * Real.exp (8 * ((C.card : ℝ) + 1))) from by ring,
          activity_exp_card_identity R C.card]
        ring

/-! ### K3c — the strong-induction assembly and the capstone -/

/-- **K3c — the induction, quantified over all graphs with `G.maxDegree ≤ Δ`.**  The graph
quantifier is essential: the recursion re-enters at `Gavoid G C` (a different graph on the same
`ι`), and every constant is keyed to the uniform cap `Δ`, never to `G.maxDegree`.  Strong induction
on `k = |A|`; `A = ∅` is the base (`Q_∅/Q_∅ = 1`); for nonempty `A` peel one anchored component
(K1), bound each `B`-block by K2c whose per-component hypothesis is K3b fed by the IH on the deleted
graph `Gavoid G C` at the strictly smaller boundary `A ∖ B`, and close with K3a. -/
theorem generalRatio_norm_le_of_card (Δ : ℕ) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) (twoPointHTActivityRadius Δ)) (k : ℕ) :
    ∀ (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet],
      G.maxDegree ≤ Δ → ∀ A : Finset ι, A.card = k →
        ‖htSubgraphSum G A t / htSubgraphSum G (∅ : Finset ι) t‖
          ≤ generalRatioBoundFun Δ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ hΔ A hcard
    classical
    set R : ℝ := twoPointHTActivityRadius Δ with hRdef
    have hRpos : 0 < R := by rw [hRdef]; exact twoPointHTActivityRadius_pos Δ
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    have htRle : ‖t‖ ≤ R := by
      have h := ht; rw [Metric.mem_ball, dist_zero_right] at h; exact le_of_lt h
    have hΔcast : (G.maxDegree : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
    have hsq : (G.maxDegree : ℝ) ^ 2 ≤ (Δ : ℝ) ^ 2 := by gcongr
    have hRkpΔ64 : (Δ : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 := by
      rw [hRdef]; exact twoPointHTActivityRadius_kp_threshold Δ
    have hRexpR_nonneg : (0 : ℝ) ≤ Real.exp 1 * R :=
      mul_nonneg (le_of_lt (Real.exp_pos 1)) hRnonneg
    have hRkpG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 64 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsq hRexpR_nonneg) hRkpΔ64
    have hRkpG6 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 / 6 := by linarith
    obtain ⟨hkpR, hρR⟩ := kp_tail_conditions_of_lt hRkpG6
    have httG64 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖t‖) < 1 / 64 := by
      refine lt_of_le_of_lt ?_ hRkpG64
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left htRle (le_of_lt (Real.exp_pos 1))
    have haNonneg : (0 : ℝ) ≤ R * Real.exp 8 := mul_nonneg hRnonneg (le_of_lt (Real.exp_pos 8))
    have hqΔ : (R * Real.exp 8) * ((Δ : ℝ) ^ 2) < 1 := by
      have h := twoPointHTActivityRadius_hq_threshold Δ
      rw [← hRdef] at h; exact h
    have hqG : (R * Real.exp 8) * ((G.maxDegree : ℝ) ^ 2) < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsq haNonneg) hqΔ
    have hQ0Gne : htSubgraphSum G (∅ : Finset ι) t ≠ 0 := by
      rw [htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex G hRpos hkpR hρR ht]
      exact Complex.exp_ne_zero _
    rcases Finset.eq_empty_or_nonempty A with rfl | hAne
    · obtain rfl : k = 0 := by simpa using hcard.symm
      rw [generalRatioBoundFun_zero, div_self hQ0Gne, norm_one]
    · obtain ⟨a₀, ha₀A⟩ := hAne
      rw [htSubgraphSum_anchored_peel G ha₀A t, Finset.sum_div]
      refine le_trans (norm_sum_le _ _)
        (le_trans (Finset.sum_le_sum (fun B hB => ?_))
          ((generalRatioBoundFun_closing Δ ha₀A).trans_eq (by rw [hcard])))
      rw [evenSubsetsThrough, Finset.mem_filter, Finset.mem_powerset] at hB
      obtain ⟨hBA, ha₀B, _hBeven⟩ := hB
      have hbound : ∀ C ∈ connectedComponentsWithBoundary G B,
          ‖t‖ ^ C.card *
            ‖htSubgraphSumAvoiding' G C (A \ B) t / htSubgraphSum G (∅ : Finset ι) t‖
            ≤ (generalRatioBoundFun Δ (A \ B).card * Real.exp 8) * (R * Real.exp 8) ^ C.card := by
        intro C hC
        rw [connectedComponentsWithBoundary, Finset.mem_filter, Finset.mem_powerset] at hC
        obtain ⟨hCsub, hCne, hCconn, _hCbd⟩ := hC
        have hgav_deg : (Gavoid G C).maxDegree ≤ Δ := le_trans (maxDegree_Gavoid_le G C) hΔ
        have hlt : (A \ B).card < k := by
          have hssub : A \ B ⊂ A := by
            rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
            exact ⟨a₀, ha₀A, fun hmem => (Finset.mem_sdiff.mp hmem).2 ha₀B⟩
          have h1 : (A \ B).card < A.card := Finset.card_lt_card hssub
          rwa [hcard] at h1
        have hIH := ih (A \ B).card hlt (Gavoid G C) hgav_deg (A \ B) rfl
        exact perComponent_avoiding'_ratio_le G C (A \ B) hRpos hkpR hρR httG64 ht
          hCsub hCne hCconn (generalRatioBoundFun Δ (A \ B).card)
          (generalRatioBoundFun_nonneg Δ _) hIH
      have hnum_nonneg : 0 ≤ generalRatioBoundFun Δ (A \ B).card * Real.exp 8 :=
        mul_nonneg (generalRatioBoundFun_nonneg Δ _) (le_of_lt (Real.exp_pos 8))
      have hK2c := boundaryComponentRatio_norm_le_geometric G ha₀B t
        (generalRatioBoundFun Δ (A \ B).card * Real.exp 8) (R * Real.exp 8)
        hnum_nonneg haNonneg hbound hqG
      refine hK2c.trans ?_
      have hdenΔpos : 0 < 1 - (R * Real.exp 8) * ((Δ : ℝ) ^ 2) := by linarith [hqΔ]
      have hdenle : 1 - (R * Real.exp 8) * ((Δ : ℝ) ^ 2)
          ≤ 1 - (R * Real.exp 8) * ((G.maxDegree : ℝ) ^ 2) := by
        have hgΔ : (R * Real.exp 8) * ((G.maxDegree : ℝ) ^ 2)
            ≤ (R * Real.exp 8) * ((Δ : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsq haNonneg
        linarith
      calc
        (generalRatioBoundFun Δ (A \ B).card * Real.exp 8)
            / (1 - (R * Real.exp 8) * ((G.maxDegree : ℝ) ^ 2))
          ≤ (generalRatioBoundFun Δ (A \ B).card * Real.exp 8)
            / (1 - (R * Real.exp 8) * ((Δ : ℝ) ^ 2)) :=
            div_le_div_of_nonneg_left hnum_nonneg hdenΔpos hdenle
        _ = twoPointHTBoundValue Δ * generalRatioBoundFun Δ (A \ B).card := by
            unfold twoPointHTBoundValue
            rw [← hRdef]; ring

/-- **K3 — the volume-uniform general-boundary ratio bound** (GJ Theorem 17.6.1, p.313; the crux of
issue #4404).  For a degree cap `Δ` and activity `t` on the Kotecký–Preiss high-temperature window
`‖t‖ < twoPointHTActivityRadius Δ`, for *every* graph `G` with `G.maxDegree ≤ Δ` and *every*
boundary `A`, the general-boundary correlation ratio obeys the graph-free finite bound
`‖Q_A(G,t)/Q_∅(G,t)‖ ≤ generalRatioBoundFun Δ |A|`.  The bound is volume-uniform (independent of
`ι`, `G`, the exhaustion stage and the actual `G.maxDegree`); it blows up in `|A|`, which is
harmless since the observable fixes `A`.  Unconditional on the KP window — the same legitimate
hypotheses as the pair capstone `correlationComplex_two_point_norm_le_of_high_temp`. -/
theorem generalRatio_norm_le (Δ : ℕ) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) (twoPointHTActivityRadius Δ))
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hΔ : G.maxDegree ≤ Δ) (A : Finset ι) :
    ‖htSubgraphSum G A t / htSubgraphSum G (∅ : Finset ι) t‖
      ≤ generalRatioBoundFun Δ A.card :=
  generalRatio_norm_le_of_card Δ ht A.card G hΔ A rfl

end IsingModel
