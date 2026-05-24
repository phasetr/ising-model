import IsingModel.BallBoundarySimonLieb.WeakBound

/-!
# Ball-boundary Simon-Lieb tight bound wrappers

Tight ball-boundary Simon-Lieb inequality layer.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Tight ball-boundary inequality (Step 137 support)

The tight form removes the extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term using Lebowitz for the scaled model.
-/

/-- **Odd-cardinality scaled correlations vanish at `h = 0`**:
The scaled model has global spin-flip symmetry when `h = 0`,
so `⟨σ^A⟩_s = 0` for odd `|A|`. -/
theorem scaledCorrelation_odd_vanish (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hh : p.h = 0)
    (s : ℝ) (A : Finset ι) (hodd : Odd A.card) :
    scaledCorrelation G E₀ p s A = 0 := by
  simp only [scaledCorrelation, scaledGibbsExpectation]
  suffices hsum : ∑ σ : Config ι,
      spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ = 0 by
    rw [hsum, mul_zero]
  -- Scaled Boltzmann weight is flip-invariant at h=0
  have hbw : ∀ σ : Config ι,
      scaledBoltzmannWeight G E₀ p s σ.flip = scaledBoltzmannWeight G E₀ p s σ := by
    intro σ
    simp only [scaledBoltzmannWeight, boltzmannWeight, hamiltonian_flip_eq G p hh σ]
    simp_rw [edgeSpin_flip]
  -- spinProduct negates under flip for odd |A|
  have hflip : ∀ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip =
      -(spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ) := by
    intro σ
    rw [hbw σ]
    have hsp : spinProduct A σ.flip = (-1 : ℝ) ^ A.card * spinProduct A σ := by
      simp only [spinProduct, Config.flip]
      simp_rw [Spin.toSign_flip, Int.cast_neg]
      exact Finset.prod_neg _
    rw [hsp]; obtain ⟨k, hk⟩ := hodd; rw [hk]; ring_nf; simp
  -- Reindex via flip: sum = -sum → sum = 0
  let flipEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩
  have hreindex : ∑ σ : Config ι,
      spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ =
    ∑ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip :=
    (Equiv.sum_comp flipEquiv _).symm
  have hsum2 : ∑ σ : Config ι,
      spinProduct A σ.flip * scaledBoltzmannWeight G E₀ p s σ.flip =
    -(∑ σ : Config ι, spinProduct A σ * scaledBoltzmannWeight G E₀ p s σ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun σ _ => hflip σ)
  linarith [hreindex.trans hsum2]

/-- **Cor. 4.3.3 for the scaled model** (new independent axiom).

For ferromagnetic `p` with `h = 0`, `s ≥ 0`, and four distinct sites `r, a, k, l`:
`scaledCorrelation G E₀ p s (symmDiff {r,a} {k,l}) ≤`
`  scaledCorrelation G E₀ p s {r,a} · scaledCorrelation G E₀ p s {k,l}`
`+ scaledCorrelation G E₀ p s {r,k} · scaledCorrelation G E₀ p s {a,l}`
`+ scaledCorrelation G E₀ p s {r,l} · scaledCorrelation G E₀ p s {a,k}`

This is a **new independent axiom** for models with non-uniform couplings
(`J_e = sJ` for `e ∈ E₀`, `J_e = J` for `e ∉ E₀`). It is mathematically valid via
the φ⁴ approximation argument (same structure as `lebowitz_four` + Cor. 4.3.3 in GHS.lean):
(1) `lebowitz_four_scaled` (a 4-site Lebowitz axiom for the scaled model);
(2) At `h = 0`, 1-point and 3-point scaled correlations vanish (`scaledCorrelation_odd_vanish`);
(3) The symmDiff form follows from `{r,a} ∩ {k,l} = ∅`.
The current repo's `lebowitz_four` covers only uniform couplings and does not directly apply.

References: Glimm–Jaffe §4.3 Cor. 4.3.3 (p. 61); cf. `cor_4_3_3` and `lebowitz_four` in GHS.lean. -/
axiom cor_4_3_3_scaled (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (s : ℝ) (hs : 0 ≤ s) (r a k l : ι)
    (hra : r ≠ a) (hrk : r ≠ k) (hrl : r ≠ l)
    (hak : a ≠ k) (hal : a ≠ l) (hkl : k ≠ l) :
    scaledCorrelation G E₀ p s (symmDiff {r, a} {k, l}) ≤
    scaledCorrelation G E₀ p s {r, a} * scaledCorrelation G E₀ p s {k, l} +
    scaledCorrelation G E₀ p s {r, k} * scaledCorrelation G E₀ p s {a, l} +
    scaledCorrelation G E₀ p s {r, l} * scaledCorrelation G E₀ p s {a, k}

/-- **Tight Lebowitz bound for the scaled model** (disjoint case, h=0):
`⟨σ^{AΔe}⟩_s − ⟨σ^A⟩_s·⟨σ^e⟩_s ≤ ⟨σ_r σ_k⟩_s·⟨σ_a σ_l⟩_s + ⟨σ_r σ_l⟩_s·⟨σ_a σ_k⟩_s`
for `A = {r,a}`, `e = {k,l}` disjoint (4 distinct sites). -/
theorem summand_le_lebowitz_of_disjoint_scaled (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (r a k l : ι) (hra : r ≠ a) (hrk : r ≠ k) (hrl : r ≠ l)
    (hak : a ≠ k) (hal : a ≠ l) (hkl : k ≠ l) :
    scaledCorrelation G E₀ p s (symmDiff {r, a} {k, l}) -
    scaledCorrelation G E₀ p s {r, a} * scaledCorrelation G E₀ p s {k, l} ≤
    scaledCorrelation G E₀ p s {r, k} * scaledCorrelation G E₀ p s {a, l} +
    scaledCorrelation G E₀ p s {r, l} * scaledCorrelation G E₀ p s {a, k} := by
  have h := cor_4_3_3_scaled G E₀ hE₀_sub p hf hh s hs r a k l hra hrk hrl hak hal hkl
  linarith

/-- The tight derivative bound constant (no extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term). -/
noncomputable def derivBoundTight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (r s : ι) : ℝ :=
  p.β * p.J * ∑ e ∈ E₀,
    Sym2.lift ⟨fun k l =>
      correlation G p {r, k} * correlation G p {s, l} +
      correlation G p {r, l} * correlation G p {s, k},
    fun k l => by simp only [Finset.pair_comm]; ring⟩ e

/-- The tight derivative bound is non-negative. -/
private lemma derivBoundTight_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r s : ι) :
    0 ≤ derivBoundTight G E₀ p r s := by
  unfold derivBoundTight
  apply mul_nonneg (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_nonneg; intro e _
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  apply add_nonneg
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)
  · exact mul_nonneg (gks_first G p hf _) (gks_first G p hf _)

/-- The tight upper bound on `d/ds ⟨σ_r σ_s⟩_s` (without extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩`). -/
private theorem scaledCorrelation_pair_deriv_le_derivBoundTight
    (G : SimpleGraph ι) [Fintype G.edgeSet]
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
    derivBoundTight G E₀ p r s := by
  unfold derivBoundTight
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum; intro e he
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  have hkl : k ≠ l := by
    intro h; subst h; exact hE₀_nd _ he (Sym2.mk_isDiag_iff.mpr rfl)
  have hrk : r ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_left r l)
  have hrl : r ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).1 (Sym2.mem_mk_right k r)
  have hsk : s ≠ k := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_left s l)
  have hsl : s ≠ l := by
    intro h; subst h; exact (hE₀_sep _ he).2 (Sym2.mem_mk_right k s)
  have hf' : Ferromagnetic (⟨p.J, 0, p.β⟩ : IsingParams ℝ) := ⟨hf.hJ, le_refl 0, hf.hβ⟩
  -- Use tight Lebowitz for scaled model
  have hleb := summand_le_lebowitz_of_disjoint_scaled G E₀ hE₀_sub p hf hh t ht0
                 r s k l hrs hrk hrl hsk hsl hkl
  -- Monotonicity: scaled correlation at t ≤ correlation at 1 = full correlation
  have hmono_rk : scaledCorrelation G E₀ p t {r, k} ≤ correlation G p {r, k} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {r, k}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_sl : scaledCorrelation G E₀ p t {s, l} ≤ correlation G p {s, l} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {s, l}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_rl : scaledCorrelation G E₀ p t {r, l} ≤ correlation G p {r, l} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {r, l}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hmono_sk : scaledCorrelation G E₀ p t {s, k} ≤ correlation G p {s, k} := by
    have := scaledCorrelation_monotoneOn G E₀ hE₀_nd hE₀_sub p hf {s, k}
      (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr zero_le_one) ht1
    simp only [scaledCorrelation_one] at this; exact this
  have hnn_rk : 0 ≤ scaledCorrelation G E₀ p t {r, k} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_sl : 0 ≤ scaledCorrelation G E₀ p t {s, l} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_rl : 0 ≤ scaledCorrelation G E₀ p t {r, l} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  have hnn_sk : 0 ≤ scaledCorrelation G E₀ p t {s, k} :=
    scaledCorrelation_nonneg G E₀ hE₀_sub p hf t ht0 _
  calc scaledCorrelation G E₀ p t (symmDiff {r, s} {k, l}) -
        scaledCorrelation G E₀ p t {r, s} * scaledCorrelation G E₀ p t {k, l}
      ≤ scaledCorrelation G E₀ p t {r, k} * scaledCorrelation G E₀ p t {s, l} +
        scaledCorrelation G E₀ p t {r, l} * scaledCorrelation G E₀ p t {s, k} := hleb
    _ ≤ correlation G p {r, k} * correlation G p {s, l} +
        correlation G p {r, l} * correlation G p {s, k} := by
          apply add_le_add
          · exact mul_le_mul hmono_rk hmono_sl hnn_sl (gks_first G p hf _)
          · exact mul_le_mul hmono_rl hmono_sk hnn_sk (gks_first G p hf _)

/-- **Tight ball-boundary Simon-Lieb inequality** (GJ §17.8 eq. 17.8.4, tight form):

For a ferromagnetic Ising model at `h = 0`, edge subset `E₀ ⊆ G.edgeFinset`, and distinct
vertices `r, s` with `scaledCorrelation G E₀ p 0 {r, s} = 0`:

  `⟨σ_r σ_s⟩ ≤ β·J · Σ_{(k,l)∈E₀}
    [⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩]`

This is the tight form without the extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term.

Reference: Glimm–Jaffe §17.8 eq. 17.8.4–17.8.5, pp. 316–318. -/
theorem ball_boundary_simon_lieb_tight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    (h_s0_vanish : scaledCorrelation G E₀ p 0 {r, s} = 0) :
    correlation G p {r, s} ≤ derivBoundTight G E₀ p r s := by
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
      ‖derivBoundTight G E₀ p r s‖ := by
    intro t ht
    rw [Real.norm_of_nonneg
          (scaledCorrelation_deriv_nonneg' G E₀ hE₀_nd hE₀_sub p hf t ht.1 {r, s}),
        Real.norm_of_nonneg (derivBoundTight_nonneg G E₀ p hf r s)]
    exact scaledCorrelation_pair_deriv_le_derivBoundTight G E₀ hE₀_nd hE₀_sub p hf hh r s hrs
      hE₀_sep t ht.1 ht.2.le
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  rw [scaledCorrelation_one G E₀ p {r, s}, h_s0_vanish, sub_zero] at hmvt
  rw [Real.norm_of_nonneg (gks_first G p hf {r, s}),
      Real.norm_of_nonneg (derivBoundTight_nonneg G E₀ p hf r s)] at hmvt
  linarith

end IsingModel
