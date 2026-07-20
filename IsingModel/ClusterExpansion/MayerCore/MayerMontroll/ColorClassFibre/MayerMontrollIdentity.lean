import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.ClusterExpansion.Families.VertexDisjoint
import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy
import IsingModel.ClusterExpansion.MayerCore.LogTaylor
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FamilyTupleSum
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.ColorDegreeBounds

/-!
# The `r!`-to-one colour-class fibre (5/5): the Mayer–Montroll identity

Structural split (5/5) of
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre`.
This child holds the colour-degree term `colorDegreeTerm` with its vanishing lemmas, the
row and column `tsum` collapses, the double summability, and the capstones
`mayer_identity_general_t` / `mayer_identity_general_t_eventually` giving
`log Ξ = ∑ₙ mayerExpansionTerm` at finite volume.  See the
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre` facade module for the
full contents overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Colour-degree term** `C(r,k)`: the `(r,k)` contribution of the Mayer expansion,
`(-1)^(k-1)/k · ∑_ω #properSurjectiveColorings(G(ω),k)/r! · clusterSeqActivity`.  Summing over
`k ∈ Icc 1 r` gives `mayerExpansionTerm G r t`; over `r ≤ k·N` gives the `k`-th log-Taylor term. -/
noncomputable def colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
      ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
        (r.factorial : ℝ) * clusterSeqActivity t ω

/-- **`colorDegreeTerm` vanishes for `k > r`**: no surjective `k`-colouring of `Fin r` when
`r < k`, so every colour count is `0`. -/
theorem colorDegreeTerm_eq_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) {r k : ℕ} (hrk : r < k) : colorDegreeTerm G t r k = 0 := by
  rw [colorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω _ => ?_)))
  rw [properSurjectiveColorings_eq_empty_of_card_lt _ hrk, Finset.card_empty, Nat.cast_zero,
    zero_div, zero_mul]

/-- **`colorDegreeTerm` vanishes at `k = 0`**: the `1/k` factor is `1/0 = 0`. -/
theorem colorDegreeTerm_zero_right {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) : colorDegreeTerm G t r 0 = 0 := by
  rw [colorDegreeTerm, Nat.cast_zero, div_zero, zero_mul]

/-- **Row absolute sum bound**: `∑'_k |colorDegreeTerm G t r k| ≤ (r^r/r!)·A^r`.  Each row is
finitely supported (`colorDegreeTerm = 0` for `k > r` and `k = 0`), so the tsum reduces to the
finite `Icc 1 r` sum bounded by `sum_abs_colorDegreeTerm_le`. -/
theorem tsum_abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) :
    ∑' k, |colorDegreeTerm G t r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  classical
  rw [tsum_eq_sum (s := Finset.range (r + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [colorDegreeTerm_eq_zero_of_lt G t (by omega : r < k), abs_zero])]
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    simp [colorDegreeTerm_zero_right]
  · rw [show Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp), colorDegreeTerm_zero_right, abs_zero, zero_add]
    exact sum_abs_colorDegreeTerm_le G t r hr1

/-- **Double summability of the colour-degree term**: `(r,k) ↦ colorDegreeTerm G t r k` is
summable over `ℕ × ℕ` whenever `e·A < 1` (`A = ∑_{P} |t|^|P|`).  Via `summable_abs_iff` and
`summable_prod_of_nonneg`: each row is finitely supported, and the row absolute sums are
majorised by the summable `(r^r/r!)·A^r`.  Enables the capstone `tsum_comm`. -/
theorem summable_uncurry_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ)
    (hact : Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1) :
    Summable (fun p : ℕ × ℕ => colorDegreeTerm G t p.1 p.2) := by
  classical
  have hsumnn : (0 : ℝ) ≤ ∑ P ∈ allPolymers G, |t| ^ P.card :=
    Finset.sum_nonneg (fun P _ => by positivity)
  have hAabs : Real.exp 1 * |∑ P ∈ allPolymers G, |t| ^ P.card| < 1 := by
    rwa [abs_of_nonneg hsumnn]
  rw [← summable_abs_iff, summable_prod_of_nonneg (fun p => abs_nonneg _)]
  refine ⟨fun r => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range (r + 1)) (fun k hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [colorDegreeTerm_eq_zero_of_lt G t (by omega : r < k), abs_zero]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg (fun k => abs_nonneg _))
      (fun r => tsum_abs_colorDegreeTerm_le G t r) ?_
    have hpow : ∀ r : ℕ, ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r =
        ((r : ℝ) ^ r / (r.factorial : ℝ)) * |∑ P ∈ allPolymers G, |t| ^ P.card| ^ r := by
      intro r; rw [abs_of_nonneg hsumnn]
    simp_rw [hpow]
    exact summable_pow_self_div_factorial_mul_abs_pow _ hAabs

/-- **`colorDegreeTerm` vanishes when `m·|allPolymers G| < r`**: no surjective `m`-colouring of a
graph on `Fin r` whose incompatibility structure comes from `r` polymers can use more than
`m·|allPolymers G|` labels, so for `m·N < r` every colour count is `0`
(`properSurjectiveColorings_empty_of_card_lt` per `ω`).  Provides the eventual vanishing in `r`
that turns the finite log-Taylor colouring sum into a `tsum`. -/
theorem colorDegreeTerm_eq_zero_of_card_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) {r m : ℕ}
    (hr : m * (allPolymers G).card < r) : colorDegreeTerm G t r m = 0 := by
  classical
  rw [colorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω hω => ?_)))
  have hω' : ∀ i, ω i ∈ allPolymers G := fun i => Fintype.mem_piFinset.mp hω i
  rw [properSurjectiveColorings_empty_of_card_lt G hω' hr, Finset.card_empty,
    Nat.cast_zero, zero_div, zero_mul]

/-- **Mayer term as the `tsum` of its colour-degree row**: `mayerExpansionTerm G r t =
∑'_k colorDegreeTerm G t r k`.  The colour-degree row is finitely supported (`Icc 1 r`), so the
`tsum` collapses to the finite double sum of `mayerExpansionTerm_eq_double_sum`. -/
theorem mayerExpansionTerm_eq_tsum_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (r : ℕ) (t : ℝ) :
    mayerExpansionTerm G r t = ∑' k, colorDegreeTerm G t r k := by
  classical
  rw [mayerExpansionTerm_eq_double_sum,
    tsum_eq_sum (s := Finset.Icc 1 r) (fun k hk => by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le, Nat.lt_one_iff] at hk
      rcases hk with hk0 | hkr
      · rw [hk0, colorDegreeTerm_zero_right]
      · exact colorDegreeTerm_eq_zero_of_lt G t hkr)]
  rfl

/-- **Log-Taylor term as the `tsum` of its colour-degree column**: the `n`-th log-Taylor term equals
`∑'_r colorDegreeTerm G t r (n+1)`.  The colour-degree column is finitely supported
(`r ≤ (n+1)·|allPolymers G|`, by `colorDegreeTerm_eq_zero_of_card_lt`), so the `tsum` collapses to
the finite range sum of `logTaylor_term_eq_coloring`. -/
theorem logTaylorTerm_eq_tsum_colorDegreeTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
        (n + 1) =
      ∑' r, colorDegreeTerm G t r (n + 1) := by
  classical
  rw [logTaylor_term_eq_coloring,
    tsum_eq_sum (s := Finset.range ((n + 1) * (allPolymers G).card + 1)) (fun r hr => by
      rw [Finset.mem_range, not_lt] at hr
      exact colorDegreeTerm_eq_zero_of_card_lt G t
        (by omega : (n + 1) * (allPolymers G).card < r))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [colorDegreeTerm, Nat.add_sub_cancel]
  push_cast
  ring

/-- **Mayer–Montroll identity (general `t`)**: in the convergence regime, the polymer free energy
equals the sum of the Mayer expansion terms,
`polymerFreeEnergy G t = ∑'_n mayerExpansionTerm G n t` (GJ §18.4).

Proof (Fubini swap of the colour-degree double sum).  The analytic side
`polymerFreeEnergy_hasSum_via_log` gives `polymerFreeEnergy = ∑'_n logTaylorTerm n`, and each
`logTaylorTerm n = ∑'_r colorDegreeTerm G t r (n+1)` (column), while
`mayerExpansionTerm G r t = ∑'_k colorDegreeTerm G t r k` (row).  Double-summability
(`summable_uncurry_colorDegreeTerm`, valid for `e·A < 1`) licenses `tsum_comm`; the `k = 0` column
vanishes, giving the `n ↔ n+1` shift between the log-Taylor and Mayer indexings.

The two hypotheses are the genuine analytic convergence conditions: `h_abs` (`|ε(t)| < 1`) for the
`log(1+ε)` series, and `hact` (`e·A < 1`, `A = ∑_P |t|^|P|`) for the double-sum Fubini swap; both
hold in the Kotecký–Preiss / high-temperature regime. -/
theorem mayer_identity_general_t {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ}
    (h_abs : |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card| < 1)
    (hact : Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1) :
    polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t := by
  classical
  have hsum : Summable (Function.uncurry fun r k => colorDegreeTerm G t r k) :=
    summable_uncurry_colorDegreeTerm G t hact
  have hlog := polymerFreeEnergy_hasSum_via_log G h_abs
  have hg : Summable (fun k => ∑' r, colorDegreeTerm G t r k) := hsum.prod_symm.prod
  have hg0 : (∑' r, colorDegreeTerm G t r 0) = 0 := by
    simp_rw [colorDegreeTerm_zero_right]; exact tsum_zero
  -- shift the `k`-index: the `k = 0` colour column vanishes, so the log-Taylor `n`-sum
  -- (indexed by `n+1`) equals the full `k`-sum.
  have hshift : ∑' n, ∑' r, colorDegreeTerm G t r (n + 1) =
      ∑' k, ∑' r, colorDegreeTerm G t r k := by
    rw [hg.tsum_eq_zero_add]; simp only [hg0, zero_add]
  -- Fubini swap of the colour-degree double sum (licensed by double-summability).
  have hcomm : ∑' k, ∑' r, colorDegreeTerm G t r k =
      ∑' r, ∑' k, colorDegreeTerm G t r k := hsum.tsum_comm
  calc polymerFreeEnergy G t
      = ∑' n, ∑' r, colorDegreeTerm G t r (n + 1) := by
        rw [← hlog.tsum_eq]
        exact tsum_congr (fun n => logTaylorTerm_eq_tsum_colorDegreeTerm G t n)
    _ = ∑' k, ∑' r, colorDegreeTerm G t r k := hshift
    _ = ∑' r, ∑' k, colorDegreeTerm G t r k := hcomm
    _ = ∑' r, mayerExpansionTerm G r t :=
        tsum_congr (fun r => (mayerExpansionTerm_eq_tsum_colorDegreeTerm G r t).symm)

/-- **Mayer–Montroll identity, eventual form near `t = 0`**: for `t` in some neighbourhood of `0`,
`polymerFreeEnergy G t = ∑'_n mayerExpansionTerm G n t` (GJ §18.4).

Both convergence hypotheses of `mayer_identity_general_t` hold near `0`: `|ε(t)| < 1` since
`ε(t) → 0` (`vdPolymerFamilies_sum_minus_one_tendsto_zero`), and `e·A(t) < 1` since
`A(t) = ∑_P |t|^|P| → 0` (every polymer is nonempty, so `A(0) = 0` and `A` is continuous). -/
theorem mayer_identity_general_t_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      polymerFreeEnergy G t = ∑' n, mayerExpansionTerm G n t := by
  classical
  -- `|ε(t)| < 1` eventually.
  have h_abs_tendsto : Filter.Tendsto (fun t : ℝ =>
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card|)
      (nhds 0) (nhds 0) := by
    simpa using (continuous_abs.tendsto 0).comp
      (vdPolymerFamilies_sum_minus_one_tendsto_zero G)
  have h_abs_ev : ∀ᶠ t : ℝ in nhds 0,
      |∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card| < 1 :=
    h_abs_tendsto.eventually_lt_const zero_lt_one
  -- `e·A(t) < 1` eventually, where `A(t) = ∑_P |t|^|P|`.
  have hcont : Continuous
      (fun t : ℝ => Real.exp 1 * ∑ P ∈ allPolymers G, |t| ^ P.card) :=
    continuous_const.mul (continuous_finset_sum _ (fun P _ => continuous_abs.pow P.card))
  have hA0 : Real.exp 1 * ∑ P ∈ allPolymers G, |(0 : ℝ)| ^ P.card = 0 :=
    mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun P hP => by
      rw [abs_zero, zero_pow (Finset.card_ne_zero.mpr (mem_allPolymers.mp hP).nonempty)])))
  have hA : Filter.Tendsto
      (fun t : ℝ => Real.exp 1 * ∑ P ∈ allPolymers G, |t| ^ P.card) (nhds 0) (nhds 0) := by
    have h := hcont.tendsto 0
    rwa [hA0] at h
  have hact_ev : ∀ᶠ t : ℝ in nhds 0,
      Real.exp 1 * (∑ P ∈ allPolymers G, |t| ^ P.card) < 1 :=
    hA.eventually_lt_const zero_lt_one
  exact (h_abs_ev.and hact_ev).mono
    (fun t ht => mayer_identity_general_t G ht.1 ht.2)

end IsingModel
