import IsingModel.BallBoundarySimonLieb.Monotonicity

/-!
# Ball-boundary Simon-Lieb weak bound wrappers

Weak ball-boundary Simon-Lieb inequality layer.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Ball-boundary inequality -/

/-- The derivative bound constant for the ball-boundary inequality. -/
noncomputable def derivBound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (r s : ι) : ℝ :=
  p.β * p.J * ∑ e ∈ E₀,
    Sym2.lift ⟨fun k l =>
      correlation G p {r, k} * correlation G p {s, l} +
      correlation G p {r, l} * correlation G p {s, k} +
      correlation G p {r, s} * correlation G p {k, l},
    fun k l => by simp [Finset.pair_comm k l]; ring⟩ e

/-- Upper bound on `d/ds ⟨σ_r σ_s⟩_s`:
Using GKS-I (drop negative term) + 4-pt monotonicity + full-model Lebowitz. -/
private theorem scaledCorrelation_pair_deriv_le_derivBound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p.β * p.J * ∑ e ∈ E₀,
      Sym2.lift ⟨fun k l =>
        scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} *
        scaledCorrelation G E₀ p t {k, l},
      fun k l => by simp [Finset.pair_comm l k]⟩ e ≤
    derivBound G E₀ p r s := by
  unfold derivBound
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum; intro e he
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have hkl : k ≠ l := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  -- Establish p = ⟨p.J, 0, p.β⟩ since p.h = 0
  have hp_eq : p = (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := by
    cases p; simp_all
  -- Drop negative term using GKS-I for scaled model
  have hnn_prod : 0 ≤ scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l} :=
    mul_nonneg (scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 {r, s})
              (scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 {k, l})
  -- Monotonicity: scaledCorrelation_t ≤ correlation (= scaledCorrelation_1)
  have hmono : scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) ≤
      correlation G p (symmDiff {r, s} {k, l}) := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf (symmDiff {r, s} {k, l})
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  -- All 4 vertices are distinct by hE₀_sep
  have hrk : r ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_left r l)
  have hrl : r ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_right k r)
  have hsk : s ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_left s l)
  have hsl : s ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_right k s)
  -- Apply summand_le_lebowitz_of_disjoint
  have hf' : Ferromagnetic (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := ⟨hf.hJ, le_refl 0, hf.hβ⟩
  have hleb := summand_le_lebowitz_of_disjoint G p.J p.β hf' r s k l hrs hrk hrl hsk hsl hkl
  rw [← hp_eq] at hleb
  calc scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l}
      ≤ correlation G p (symmDiff {r, s} {k, l}) := by linarith
    _ ≤ correlation G p {r, k} * correlation G p {s, l} +
          correlation G p {r, l} * correlation G p {s, k} +
          correlation G p {r, s} * correlation G p {k, l} := by linarith

/-- The derivative bound is non-negative. -/
private lemma derivBound_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : ι) :
    0 ≤ derivBound G E₀ p r s := by
  unfold derivBound
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
    · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)

/-- **Ball-boundary Simon-Lieb inequality** (GJ §17.8, weak form):

For a ferromagnetic Ising model at `h = 0`, edge subset `E₀ ⊆ G.edgeFinset`, and distinct
vertices `r, s` with `scaledCorrelation G E₀ p 0 {r, s} = 0` (disconnected at s=0):

  `⟨σ_r σ_s⟩ ≤ β·J · Σ_{(k,l)∈E₀}
    [⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩ + ⟨σ_r σ_s⟩·⟨σ_k σ_l⟩]`

The extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term can be eliminated if Lebowitz holds for the
scaled model (cf. GJ §17.8 eq. 17.8.4 / `cor_4_3_3`).

Reference: Glimm–Jaffe §17.8 pp. 316–318. -/
theorem ball_boundary_simon_lieb (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (h_s0_vanish : scaledCorrelation G E₀ p 0 {r, s} = 0) :
    correlation G p {r, s} ≤ derivBound G E₀ p r s := by
  -- MVT on [0,1]: corr(r,s) = scaledCorr_1 ≤ scaledCorr_0 + derivBound = 0 + derivBound
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s' => scaledCorrelation G E₀ p s' {r, s})
        (p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e)
        (Set.Icc 0 1) t :=
    fun t _ => (hasDerivAt_scaledCorrelation G E₀ hE₀_nd p t {r, s}).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖p.β * p.J * ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            scaledCorrelation G E₀ p t (symmDiff {r, s} {u, v}) -
            scaledCorrelation G E₀ p t {r, s} *
            scaledCorrelation G E₀ p t {u, v},
          fun u v => by simp [Finset.pair_comm v u]⟩ e‖ ≤
      ‖derivBound G E₀ p r s‖ := by
    intro t ht
    rw [Real.norm_of_nonneg
          (scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf t ht.1 {r, s}),
        Real.norm_of_nonneg (derivBound_nonneg G E₀ p hf r s)]
    exact scaledCorrelation_pair_deriv_le_derivBound G E₀ hE₀_nd hE₀_sub p hf hh r s hrs
      hE₀_sep t ht.1 ht.2.le
  -- Apply MVT on [0,1]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  -- hmvt : ‖scaledCorrelation G E₀ p 1 {r,s} - scaledCorrelation G E₀ p 0 {r,s}‖ ≤ ‖derivBound ...‖
  rw [scaledCorrelation_one G E₀ p {r, s}, h_s0_vanish, sub_zero] at hmvt
  rw [Real.norm_of_nonneg (gks_first G p hf {r, s}),
      Real.norm_of_nonneg (derivBound_nonneg G E₀ p hf r s)] at hmvt
  linarith


end IsingModel
