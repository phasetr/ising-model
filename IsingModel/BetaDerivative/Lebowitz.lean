import IsingModel.BetaDerivative.CorrelationFormulas

/-!
# Lebowitz bounds for beta derivatives

This module contains the Lebowitz upper-bound layer split from
`IsingModel.BetaDerivative`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lebowitz upper bound on the β-derivative (Step 117b) -/

omit [Fintype ι] in
/-- **symmDiff of two disjoint pairs**: when `r,s,u,v` are pairwise
distinct, `{r,s} △ {u,v} = {r,s,u,v}` as Finsets. -/
private lemma symmDiff_pairs_of_disjoint
    {r s u v : ι} (hrs : r ≠ s) (hru : r ≠ u) (hrv : r ≠ v)
    (hsu : s ≠ u) (hsv : s ≠ v) (huv : u ≠ v) :
    symmDiff ({r, s} : Finset ι) {u, v} = {r, s, u, v} := by
  have h_disj : Disjoint ({r, s} : Finset ι) {u, v} := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl) (rfl | rfl)
    · exact absurd rfl hru
    · exact absurd rfl hrv
    · exact absurd rfl hsu
    · exact absurd rfl hsv
  rw [symmDiff_def, Finset.sdiff_eq_self_iff_disjoint.mpr h_disj,
      Finset.sdiff_eq_self_iff_disjoint.mpr h_disj.symm]
  ext x
  rw [Finset.sup_eq_union]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **Lebowitz bound for the β-derivative summand at non-degenerate edges**
(GJ §17.5 p.312):
For pairwise distinct sites `r,s,u,v` and ferromagnetic `h=0`:

  `⟨σ_r σ_s σ_u σ_v⟩ − ⟨σ_r σ_s⟩·⟨σ_u σ_v⟩`
  `  ≤ ⟨σ_r σ_u⟩·⟨σ_s σ_v⟩ + ⟨σ_r σ_v⟩·⟨σ_s σ_u⟩`

which bounds the summand `corr({r,s}△{u,v}) − corr({r,s})·corr({u,v})`.

Proof: `symmDiff {r,s} {u,v} = {r,s,u,v}` (disjoint) + Cor 4.3.3.

Reference: Glimm–Jaffe §17.5 p.312 (2nd ed.); Cor. 4.3.3 (Lebowitz). -/
theorem summand_le_lebowitz_of_disjoint
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (r s u v : ι) (hrs : r ≠ s) (hru : r ≠ u) (hrv : r ≠ v)
    (hsu : s ≠ u) (hsv : s ≠ v) (huv : u ≠ v) :
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v} ≤
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, u} := by
  rw [symmDiff_pairs_of_disjoint hrs hru hrv hsu hsv huv]
  have h := cor_4_3_3 G J β hf r s u v hrs hru hrv hsu hsv huv
  unfold truncated4 at h
  linarith

/-- **Upper bound on each derivative summand**:
For any edge `e ∈ G.edgeFinset` and distinct `r, s`, the summand
`corr({r,s}△{e₁,e₂}) − corr({r,s})·corr({e₁,e₂})` in the
β-derivative formula satisfies a one-sided bound ≤ 1.

Proof: GKS-I gives all correlations ≥ 0, and all correlations ≤ 1
(from `abs_correlation_le_one`). The summand is ≥ 0 by GKS-II and ≤ 1.

Reference: Glimm–Jaffe §17.5 p.312 (2nd ed.). -/
lemma summand_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (A B : Finset ι) :
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) -
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B ≤ 1 := by
  have h_sd : |correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B)| ≤ 1 :=
    abs_correlation_le_one G ⟨J, 0, β⟩ (symmDiff A B)
  have h_A : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A :=
    gks_first G ⟨J, 0, β⟩ hf A
  have h_B : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B :=
    gks_first G ⟨J, 0, β⟩ hf B
  have h_pos : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) :=
    gks_first G ⟨J, 0, β⟩ hf (symmDiff A B)
  linarith [abs_le.mp h_sd, mul_nonneg h_A h_B]

/-- **Lebowitz upper bound on β-derivative of 2-point function** (GJ §17.5 p.312):
The derivative `d/dβ ⟨σ_r σ_s⟩_β` at `h = 0` satisfies:

  `d/dβ ⟨σ_r σ_s⟩ ≤ J · Σ_{e∈E} [⟨σ_r σ_{e₁}⟩·⟨σ_s σ_{e₂}⟩ + ⟨σ_r σ_{e₂}⟩·⟨σ_s σ_{e₁}⟩]`
  `                  + J · |E(G)|`

The extra `J·|E(G)|` term is a coarse upper bound for degenerate edges
(those incident to `r` or `s`), for which the standard Lebowitz bound does not
apply directly. Since at most `deg(r) + deg(s)` edges are degenerate, a tighter
bound is `J·(deg(r) + deg(s))` — for ℤ^d nearest-neighbour, this is `J·4d`.

Reference: Glimm–Jaffe §17.5 pp.311–312 (2nd ed.); Cor. 4.3.3 (Lebowitz). -/
theorem correlation_beta_deriv_le_lebowitz
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) d β ∧
      d ≤ J * ∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v =>
              correlation G p {r, u} * correlation G p {s, v} +
              correlation G p {r, v} * correlation G p {s, u},
            fun u v => by ring⟩ e
        + J * G.edgeFinset.card := by
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_beta G J β {r, s}, ?_⟩
  -- Goal: J * Σ_e [summand_e] ≤ J * Σ_e [lebowitz_e] + J * |E|
  have hcard : (G.edgeFinset.card : ℝ) = ∑ _ ∈ G.edgeFinset, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hJ
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
  have huv : u ≠ v := by
    intro heq; subst heq; exact (SimpleGraph.mem_edgeFinset.mp he).ne rfl
  simp only [Sym2.lift_mk]
  -- summand_e ≤ lebowitz_e + 1
  -- Use Lebowitz if non-degenerate; trivial bound otherwise
  by_cases hru : r = u
  · subst hru
    -- Degenerate: r = u. summand ≤ 1 ≤ lebowitz + 1
    have h1 := summand_le_one G J β hf {r, s} {r, v}
    have h2 : 0 ≤ correlation G p {r, r} * correlation G p {s, v} +
                   correlation G p {r, v} * correlation G p {s, r} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hrv : r = v
  · subst hrv
    have h1 := summand_le_one G J β hf {r, s} {u, r}
    have h2 : 0 ≤ correlation G p {r, u} * correlation G p {s, r} +
                   correlation G p {r, r} * correlation G p {s, u} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hsu : s = u
  · subst hsu
    have h1 := summand_le_one G J β hf {r, s} {s, v}
    have h2 : 0 ≤ correlation G p {r, s} * correlation G p {s, v} +
                   correlation G p {r, v} * correlation G p {s, s} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  by_cases hsv : s = v
  · subst hsv
    have h1 := summand_le_one G J β hf {r, s} {u, s}
    have h2 : 0 ≤ correlation G p {r, u} * correlation G p {s, s} +
                   correlation G p {r, s} * correlation G p {s, u} :=
      add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                 (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
    linarith
  -- Non-degenerate case: r,s,u,v pairwise distinct
  have h_le := summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
  linarith [show (0 : ℝ) ≤ 1 from zero_le_one]

/-- **Tight Lebowitz upper bound on β-derivative of 2-point function** (Step 154, GJ §17.5):
The derivative `d/dβ ⟨σ_r σ_s⟩_β` satisfies:
`d ≤ J · ∑_{e∈E} lebowitz_e + J · |{e ∈ E(G) : r ∈ e ∨ s ∈ e}|`.

Improves `correlation_beta_deriv_le_lebowitz` (Step 117b): the error is now proportional
to the number of edges **incident to r or s** only (≤ deg(r) + deg(s) ≤ 4d for ℤ^d),
not the full edge count |E(G)|. This makes the bound usable in the infinite-volume limit
where |E| → ∞ but the number of incident edges stays bounded.

Key insight: for non-degenerate edges {u,v} (r,s,u,v all distinct), `summand ≤ lebowitz`
exactly (no +1). Only degenerate edges (incident to r or s) need the `+1` correction.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem correlation_beta_deriv_le_lebowitz_tight
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (r s : ι) (hrs : r ≠ s) :
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∃ d : ℝ,
      HasDerivAt (fun β' => correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) d β ∧
      d ≤ J * ∑ e ∈ G.edgeFinset,
              Sym2.lift ⟨fun u v =>
                  correlation G p {r, u} * correlation G p {s, v} +
                  correlation G p {r, v} * correlation G p {s, u},
                fun u v => by ring⟩ e
          + J * (G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card := by
  classical
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_beta G J β {r, s}, ?_⟩
  -- Abbreviate the summand and Lebowitz functions
  set leb : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G p {r, u} * correlation G p {s, v} +
                           correlation G p {r, v} * correlation G p {s, u},
              fun u v => by ring⟩ e
  set summ : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e
  -- Step 1: bound ∑_e summ ≤ ∑_e leb + |{e: deg}|
  set deg := G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)
  have h_leb_nn : ∀ e ∈ G.edgeFinset, 0 ≤ leb e := fun e _ => by
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    exact add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                     (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
  have h_bound : ∑ e ∈ G.edgeFinset, summ e ≤ ∑ e ∈ G.edgeFinset, leb e + deg.card := by
    have split := (Finset.sum_filter_add_sum_filter_not G.edgeFinset
      (fun e => r ∈ e ∨ s ∈ e) summ).symm
    rw [split]
    -- deg part: ∑_{deg} summ ≤ ∑_{deg} 1 = |deg|
    -- non-deg part: ∑_{non-deg} summ ≤ ∑_{non-deg} leb ≤ ∑_e leb
    have h1 : ∑ e ∈ deg, summ e ≤ deg.card := by
      rw [show (deg.card : ℝ) = ∑ _ ∈ deg, 1 from by simp]
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heE, hmem⟩ := he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      simp only [Sym2.lift_mk, Sym2.mem_iff, summ] at hmem ⊢
      rcases hmem with (hru | hrv) | (hsu | hsv)
      · subst hru; exact summand_le_one G J β hf {r, s} {r, v}
      · subst hrv; exact summand_le_one G J β hf {r, s} {u, r}
      · subst hsu; exact summand_le_one G J β hf {r, s} {s, v}
      · subst hsv; exact summand_le_one G J β hf {r, s} {u, s}
    have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), summ e ≤
              ∑ e ∈ G.edgeFinset, leb e :=
      calc ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), summ e
          ≤ ∑ e ∈ G.edgeFinset.filter (fun e => ¬(r ∈ e ∨ s ∈ e)), leb e := by
              apply Finset.sum_le_sum
              intro e he
              rw [Finset.mem_filter] at he
              obtain ⟨heE, hni⟩ := he
              obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
              have huv : u ≠ v := (SimpleGraph.mem_edgeFinset.mp heE).ne
              simp only [Sym2.mem_iff, not_or] at hni
              obtain ⟨⟨hru, hrv⟩, hsu, hsv⟩ := hni
              exact summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
        _ ≤ ∑ e ∈ G.edgeFinset, leb e :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun e he _ => h_leb_nn e he)
    have eq_deg : ∑ x ∈ G.edgeFinset with r ∈ x ∨ s ∈ x, summ x = ∑ e ∈ deg, summ e := rfl
    linarith
  calc J * ∑ e ∈ G.edgeFinset, summ e
      ≤ J * (∑ e ∈ G.edgeFinset, leb e + ↑(#deg)) := mul_le_mul_of_nonneg_left h_bound hJ
    _ = J * G.edgeFinset.sum leb + J * ↑(#deg) := by ring

end IsingModel
