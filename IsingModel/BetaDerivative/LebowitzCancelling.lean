import IsingModel.BetaDerivative.Lebowitz

/-!
# c-cancelling incident bound for the β-derivative Lebowitz estimate (GJ §17.5 p.312)

The tight Lebowitz β-derivative bound (`correlation_beta_deriv_le_lebowitz_tight`) bounds the
*incident* (degenerate) edge summands `corr({r,s}△{e}) − corr{r,s}·corr{e}` coarsely by `1`,
yielding a `+J·|incident|` term.  Dividing that constant by the (exponentially small) two-point
function `c = ⟨σ_r σ_s⟩` blows up, which is unsuitable for the GJ p.312 mass-continuity estimate.

This module supplies the **c-cancelling** incident bound: the incident summand is bounded by the
*reduced* correlation `corr({r,s}△{e})` (dropping the non-negative product `corr{r,s}·corr{e}`).
For an incident edge `{r,v}` this reduced correlation is `⟨σ_s σ_v⟩`, and `⟨σ_s σ_v⟩/c` stays
bounded because `v` is adjacent to `r` (so `dist(s,v) ≥ dist(r,s) − 1`).  This is GJ's `2A`
mechanism.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~312.
-/

namespace IsingModel

open Finset

/-- **c-cancelling per-summand bound.**  The β-derivative summand
`corr(A△B) − corr(A)·corr(B)` is `≤ corr(A△B)`, since the subtracted product is non-negative
(GKS-I).  This is the tight, *c-cancelling* replacement for `summand_le_one`. -/
lemma summand_le_symmDiff
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ))
    (A B : Finset ι) :
    correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) -
      correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A *
      correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B
      ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff A B) := by
  have hA : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A := gks_first G ⟨J, 0, β⟩ hf A
  have hB : 0 ≤ correlation G (⟨J, 0, β⟩ : IsingParams ℝ) B := gks_first G ⟨J, 0, β⟩ hf B
  linarith [mul_nonneg hA hB]

/-- **c-cancelling tight Lebowitz β-derivative bound** (GJ §17.5 p.312).  Same as
`correlation_beta_deriv_le_lebowitz_tight` but the incident (degenerate) edges contribute the
*reduced* correlation `corr({r,s}△{e})` (c-cancelling) instead of the coarse `1`:
`d/dβ ⟨σ_r σ_s⟩ ≤ J·∑_e leb_e + J·∑_{e incident to r or s} corr({r,s}△{e})`. -/
theorem correlation_beta_deriv_le_lebowitz_cancelling
    {ι : Type*} [DecidableEq ι] [Fintype ι]
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
          + J * ∑ e ∈ G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e),
              Sym2.lift ⟨fun u v =>
                  correlation G p (symmDiff {r, s} {u, v}),
                fun u v => by simp only [Finset.pair_comm u v]⟩ e := by
  classical
  intro p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  refine ⟨_, hasDerivAt_correlation_beta G J β {r, s}, ?_⟩
  set leb : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G p {r, u} * correlation G p {s, v} +
                           correlation G p {r, v} * correlation G p {s, u},
              fun u v => by ring⟩ e with hleb_def
  set summ : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G (⟨J, 0, β⟩ : IsingParams ℝ) (symmDiff {r, s} {u, v}) -
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, s} *
                           correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {u, v},
              fun u v => by simp [Finset.pair_comm v u]⟩ e with hsumm_def
  set inc : Sym2 ι → ℝ := fun e =>
    Sym2.lift ⟨fun u v => correlation G p (symmDiff {r, s} {u, v}),
              fun u v => by simp only [Finset.pair_comm u v]⟩ e with hinc_def
  set deg := G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e) with hdeg_def
  have h_leb_nn : ∀ e ∈ G.edgeFinset, 0 ≤ leb e := fun e _ => by
    obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
    exact add_nonneg (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
                     (mul_nonneg (gks_first G p hf _) (gks_first G p hf _))
  have h_bound : ∑ e ∈ G.edgeFinset, summ e
      ≤ ∑ e ∈ G.edgeFinset, leb e + ∑ e ∈ deg, inc e := by
    have split := (Finset.sum_filter_add_sum_filter_not G.edgeFinset
      (fun e => r ∈ e ∨ s ∈ e) summ).symm
    rw [split]
    have h1 : ∑ e ∈ deg, summ e ≤ ∑ e ∈ deg, inc e := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      simp only [Sym2.lift_mk, summ, inc]
      exact summand_le_symmDiff G J β hf {r, s} {u, v}
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
              simp only [Sym2.lift_mk, summ, leb]
              exact summand_le_lebowitz_of_disjoint G J β hf r s u v hrs hru hrv hsu hsv huv
        _ ≤ ∑ e ∈ G.edgeFinset, leb e :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun e he _ => h_leb_nn e he)
    have eq_deg : ∑ x ∈ G.edgeFinset with r ∈ x ∨ s ∈ x, summ x = ∑ e ∈ deg, summ e := rfl
    linarith
  calc J * ∑ e ∈ G.edgeFinset, summ e
      ≤ J * (∑ e ∈ G.edgeFinset, leb e + ∑ e ∈ deg, inc e) :=
        mul_le_mul_of_nonneg_left h_bound hJ
    _ = J * ∑ e ∈ G.edgeFinset, leb e + J * ∑ e ∈ deg, inc e := by ring

end IsingModel
