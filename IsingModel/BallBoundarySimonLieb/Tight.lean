import IsingModel.BallBoundarySimonLieb.WeakBound
import IsingModel.Inequalities.Lebowitz.ScaledLebowitz

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

/-- **Cor. 4.3.3 for the scaled model** (proven; formerly an axiom).

For ferromagnetic `p` with `h = 0`, `s ≥ 0`, and four distinct sites `r, a, k, l`:
`scaledCorrelation G E₀ p s (symmDiff {r,a} {k,l}) ≤`
`  scaledCorrelation G E₀ p s {r,a} · scaledCorrelation G E₀ p s {k,l}`
`+ scaledCorrelation G E₀ p s {r,k} · scaledCorrelation G E₀ p s {a,l}`
`+ scaledCorrelation G E₀ p s {r,l} · scaledCorrelation G E₀ p s {a,k}`

Proof: the abstract-weight duplicate-variable layer. The scaled fourfold
weight has non-negative u-moments
(`Lebowitz.hasNonnegUMoments_wQuadWeight_scaled` — the per-edge coefficients
`β·s·J/4` on `E₀` and `β·J/4` elsewhere are all non-negative for `s ≥ 0`),
so the generic `tq` comparison inequality (`Lebowitz.wCor_4_3_2_tq`) applies
at `A = {r,a}`, `B = {k,l}`; the powerset formulas evaluate over the two
pairs and the zero-field odd scaled correlations vanish
(`scaledCorrelation_odd_vanish`). This was formerly a *new independent
axiom*; it is now a theorem (GJ §4.3 Cor 4.3.3 for non-uniform couplings,
p. 61). -/
theorem cor_4_3_3_scaled (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (s : ℝ) (hs : 0 ≤ s) (r a k l : ι)
    (hra : r ≠ a) (hrk : r ≠ k) (hrl : r ≠ l)
    (hak : a ≠ k) (hal : a ≠ l) (hkl : k ≠ l) :
    scaledCorrelation G E₀ p s (symmDiff {r, a} {k, l}) ≤
    scaledCorrelation G E₀ p s {r, a} * scaledCorrelation G E₀ p s {k, l} +
    scaledCorrelation G E₀ p s {r, k} * scaledCorrelation G E₀ p s {a, l} +
    scaledCorrelation G E₀ p s {r, l} * scaledCorrelation G E₀ p s {a, k} := by
  have hw : ∀ σ : Config ι, 0 < scaledBoltzmannWeight G E₀ p s σ :=
    scaledBoltzmannWeight_pos G E₀ p s
  have hmom :=
    Lebowitz.hasNonnegUMoments_wQuadWeight_scaled G E₀ hE₀_sub p hf s hs
  have htq := Lebowitz.wCor_4_3_2_tq _ hw hmom {r, a} {k, l}
  rw [Lebowitz.wDoubleExpectation_tProd _ hw,
    Lebowitz.wDoubleExpectation_qProd _ hw,
    Lebowitz.wDoubleExpectation_tProd_mul_qProd _ hw {r, a} {k, l}
      (by simp [Finset.disjoint_left, hrk, hrl, hak, hal])] at htq
  simp only [Lebowitz.sum_powerset_pair hra,
    Lebowitz.sum_powerset_pair hkl] at htq
  have hbridge : ∀ X : Finset ι,
      Lebowitz.wCorrelation (scaledBoltzmannWeight G E₀ p s) X
        = scaledCorrelation G E₀ p s X := fun X => rfl
  simp only [hbridge] at htq
  have hempty : scaledCorrelation G E₀ p s ∅ = 1 := by
    unfold scaledCorrelation scaledGibbsExpectation
    rw [show ∑ σ : Config ι,
        spinProduct ∅ σ * scaledBoltzmannWeight G E₀ p s σ
        = scaledPartitionFunction G E₀ p s from by
      unfold scaledPartitionFunction
      exact Finset.sum_congr rfl fun σ _ => by rw [spinProduct_empty, one_mul]]
    field_simp [(scaledPartitionFunction_pos G E₀ p s).ne']
  simp only [Finset.sdiff_empty, Finset.sdiff_self,
    Lebowitz.pair_sdiff_left hra, Lebowitz.pair_sdiff_right hra,
    Lebowitz.pair_sdiff_left hkl, Lebowitz.pair_sdiff_right hkl,
    Finset.empty_union, Finset.union_empty, Finset.singleton_union,
    Finset.insert_union, Finset.card_empty, Finset.card_singleton,
    hempty] at htq
  have hcard_kl : ({k, l} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hkl]), Finset.card_singleton]
  rw [hcard_kl] at htq
  norm_num at htq
  have hv_r : scaledCorrelation G E₀ p s {r} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {r} ⟨0, by simp⟩
  have hv_a : scaledCorrelation G E₀ p s {a} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {a} ⟨0, by simp⟩
  have hv_k : scaledCorrelation G E₀ p s {k} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {k} ⟨0, by simp⟩
  have hv_l : scaledCorrelation G E₀ p s {l} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {l} ⟨0, by simp⟩
  have hv_rak : scaledCorrelation G E₀ p s {r, a, k} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {r, a, k} ⟨1, by
      simp [Finset.card_insert_of_notMem, hra, hrk, hak]⟩
  have hv_ral : scaledCorrelation G E₀ p s {r, a, l} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {r, a, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hra, hrl, hal]⟩
  have hv_rkl : scaledCorrelation G E₀ p s {r, k, l} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {r, k, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hrk, hrl, hkl]⟩
  have hv_akl : scaledCorrelation G E₀ p s {a, k, l} = 0 :=
    scaledCorrelation_odd_vanish G E₀ p hh s {a, k, l} ⟨1, by
      simp [Finset.card_insert_of_notMem, hak, hal, hkl]⟩
  rw [hv_r, hv_a, hv_k, hv_l, hv_rak, hv_ral, hv_rkl, hv_akl] at htq
  have hd : Disjoint ({r, a} : Finset ι) {k, l} := by
    simp [Finset.disjoint_left, hrk, hrl, hak, hal]
  have hsd : symmDiff ({r, a} : Finset ι) {k, l} = {r, a, k, l} := by
    rw [hd.symmDiff_eq_sup]
    change ({r, a} : Finset ι) ∪ {k, l} = {r, a, k, l}
    rw [show ({r, a} : Finset ι) = insert r {a} from rfl,
      Finset.insert_union, Finset.singleton_union]
  rw [hsd]
  nlinarith [htq]

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

/-- **Tight finite-volume coupling difference bound**: the `s = 1` minus `s = 0`
scaled-correlation difference is at most the *tight* ball-boundary derivative
bound `derivBoundTight` (no extra `⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` diagonal term). This is the
tight analogue of `scaledCorrelation_one_sub_zero_le_derivBound`
(`WeakBound.lean`); same mean-value argument, but the per-`t` derivative is bounded
by `derivBoundTight` via `scaledCorrelation_pair_deriv_le_derivBoundTight` (which
drops the diagonal term using `cor_4_3_3_scaled`). Dropping the diagonal term is
what makes the resulting per-stage increment *summable* over an exhaustion's cut
edges (Issue #2965, Phase A→B). -/
theorem scaledCorrelation_one_sub_zero_le_derivBoundTight (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e) :
    scaledCorrelation G E₀ p 1 {r, s} - scaledCorrelation G E₀ p 0 {r, s}
      ≤ derivBoundTight G E₀ p r s := by
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
  rw [Real.norm_of_nonneg (derivBoundTight_nonneg G E₀ p hf r s)] at hmvt
  calc scaledCorrelation G E₀ p 1 {r, s} - scaledCorrelation G E₀ p 0 {r, s}
      ≤ |scaledCorrelation G E₀ p 1 {r, s} - scaledCorrelation G E₀ p 0 {r, s}| :=
        le_abs_self _
    _ = ‖scaledCorrelation G E₀ p 1 {r, s} - scaledCorrelation G E₀ p 0 {r, s}‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ derivBoundTight G E₀ p r s := hmvt

/-- **Tight bond-deletion correlation increment**: adding the bond set `E₀`
(with `r, s` on no `E₀`-edge) raises the pair correlation `⟨σ_r σ_s⟩` by at most the
*tight* ball-boundary derivative bound `derivBoundTight` (cross terms only):

  `correlation G p {r,s} − correlation (G.deleteEdges ↑E₀) p {r,s}
     ≤ derivBoundTight G E₀ p r s`.

Tight analogue of `correlation_sub_deleteEdges_le_derivBound` (`WeakBound.lean`):
combines the tight mean-value difference bound with the `s = 0` bond-deleted
identification `scaledCorrelation_zero`. Because `derivBoundTight` carries only the
cross products `⟨σ_r σ_k⟩·⟨σ_s σ_l⟩ + ⟨σ_r σ_l⟩·⟨σ_s σ_k⟩` (no diagonal
`⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term), the resulting per-stage exhaustion increment is
summable under spatial decay — the form needed for the volume-convergence rate
(Issue #2965, Phase A→B). -/
theorem correlation_sub_deleteEdges_le_derivBoundTight (G : SimpleGraph ι)
    [Fintype G.edgeSet] (E₀ : Finset (Sym2 ι)) (hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag)
    (hE₀_sub : E₀ ⊆ G.edgeFinset) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hh : p.h = 0) (r s : ι) (hrs : r ≠ s)
    (hE₀_sep : ∀ e ∈ E₀, ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    [Fintype (G.deleteEdges ↑E₀).edgeSet] :
    correlation G p {r, s} - correlation (G.deleteEdges ↑E₀) p {r, s}
      ≤ derivBoundTight G E₀ p r s := by
  have h := scaledCorrelation_one_sub_zero_le_derivBoundTight G E₀ hE₀_nd hE₀_sub p hf hh
    r s hrs hE₀_sep
  rwa [scaledCorrelation_one, scaledCorrelation_zero G E₀ hE₀_sub p {r, s}] at h

/-- **`derivBoundTight` monotonicity under correlation upper bounds**: tight
analogue of `derivBound_le_of_correlation_le`. If a nonnegative
`c : ι → ι → ℝ` dominates every two-point correlation, then `derivBoundTight` is
dominated by the same edge sum (cross products only) with each correlation replaced
by `c`. Each summand is a sum of two products of nonnegative correlations
(`gks_first`), monotone under the pointwise bound (no symmetry of `c` is needed:
the cross-product summand is symmetric in `k, l` by `+`-commutativity alone).
Separates the boundary-sum decay step (Issue #2965, Phase A→B): one may substitute
`c a b =` an infinite-volume decay bound without re-touching the `derivBoundTight`
algebra. -/
theorem derivBoundTight_le_of_correlation_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (r s : ι) (c : ι → ι → ℝ)
    (hc_nonneg : ∀ a b, 0 ≤ c a b)
    (hcorr : ∀ a b, correlation G p {a, b} ≤ c a b) :
    derivBoundTight G E₀ p r s
      ≤ p.β * p.J * ∑ e ∈ E₀, Sym2.lift ⟨fun k l =>
          c r k * c s l + c r l * c s k,
          fun k l => by
            change c r k * c s l + c r l * c s k = c r l * c s k + c r k * c s l
            ring⟩ e := by
  unfold derivBoundTight
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hf.hβ.le hf.hJ)
  apply Finset.sum_le_sum
  intro e _he
  obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
  simp only [Sym2.lift_mk]
  refine add_le_add ?_ ?_
  · exact mul_le_mul (hcorr r k) (hcorr s l) (gks_first G p hf _) (hc_nonneg r k)
  · exact mul_le_mul (hcorr r l) (hcorr s k) (gks_first G p hf _) (hc_nonneg r l)

end IsingModel
