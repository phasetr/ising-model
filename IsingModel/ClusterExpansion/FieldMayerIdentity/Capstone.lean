import IsingModel.ClusterExpansion.FieldMayerIdentity.Definitions
import IsingModel.ClusterExpansion.FieldMayerIdentity.ColorDegreeTerm

/-!
# Field Mayer–Montroll identity: the L5 capstone
(GJ §17.6.1, brick 4 — child 4 of 4)

The field Mayer–Montroll capstone `field_mayer_identity_general` and its eventual
form near `a = 0`.  See `FieldMayerIdentity.lean` for the full module overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## L5: the field Mayer–Montroll capstone -/

/-- **Field Mayer–Montroll identity** (GJ §17.6.1, brick 4): in the high-temperature
convergence regime, the field polymer free energy equals the sum of the field Mayer
expansion terms,
`fieldPolymerFreeEnergy G a b = ∑'_n fieldMayerExpansionTerm G n a b`.

Proof (Fubini swap of the colour-degree double sum, exactly as the `h = 0`
`mayer_identity_general_t`).  The analytic side `fieldPolymerFreeEnergy_hasSum_via_log`
gives `fieldPolymerFreeEnergy = ∑'_n logTaylorTerm n`, and each
`logTaylorTerm n = ∑'_r fieldColorDegreeTerm G a b r (n+1)` (column), while
`fieldMayerExpansionTerm G r a b = ∑'_k fieldColorDegreeTerm G a b r k` (row).
Double-summability (`summable_uncurry_fieldColorDegreeTerm`, valid for `e·A_C < 1`)
licenses `tsum_comm`; the `k = 0` column vanishes, giving the `n ↔ n+1` shift.

The two hypotheses are the genuine analytic convergence conditions: `h_abs`
(`|ε_{a,b}| < 1`) for the `log(1+ε)` series over the erase-`∅` connected family sum,
and `hact` (`e·A_C < 1`, `A_C = ∑_P |tanh a|^|P|`, the brick-3 window) for the
double-sum Fubini swap. -/
theorem field_mayer_identity_general (G : SimpleGraph ι) [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b := by
  classical
  have hsum : Summable (Function.uncurry fun r k => fieldColorDegreeTerm G a b r k) :=
    summable_uncurry_fieldColorDegreeTerm G a b hact
  have hlog := fieldPolymerFreeEnergy_hasSum_via_log G h_abs
  have hg : Summable (fun k => ∑' r, fieldColorDegreeTerm G a b r k) := hsum.prod_symm.prod
  have hg0 : (∑' r, fieldColorDegreeTerm G a b r 0) = 0 := by
    simp_rw [fieldColorDegreeTerm_zero_right]; exact tsum_zero
  have hshift : ∑' n, ∑' r, fieldColorDegreeTerm G a b r (n + 1) =
      ∑' k, ∑' r, fieldColorDegreeTerm G a b r k := by
    rw [hg.tsum_eq_zero_add]; simp only [hg0, zero_add]
  have hcomm : ∑' k, ∑' r, fieldColorDegreeTerm G a b r k =
      ∑' r, ∑' k, fieldColorDegreeTerm G a b r k := hsum.tsum_comm
  calc fieldPolymerFreeEnergy G a b
      = ∑' n, ∑' r, fieldColorDegreeTerm G a b r (n + 1) := by
        rw [← hlog.tsum_eq]
        exact tsum_congr (fun n => fieldLogTaylorTerm_eq_tsum_fieldColorDegreeTerm G a b n)
    _ = ∑' k, ∑' r, fieldColorDegreeTerm G a b r k := hshift
    _ = ∑' r, ∑' k, fieldColorDegreeTerm G a b r k := hcomm
    _ = ∑' r, fieldMayerExpansionTerm G r a b :=
        tsum_congr (fun r => (fieldMayerExpansionTerm_eq_tsum_fieldColorDegreeTerm G r a b).symm)

/-- **Field Mayer–Montroll identity, eventual form near `a = 0`** (GJ §17.6.1,
brick 4): for fixed `b`, in some neighbourhood of `a = 0`,
`fieldPolymerFreeEnergy G a b = ∑'_n fieldMayerExpansionTerm G n a b`.

Both convergence hypotheses of `field_mayer_identity_general` hold as `a → 0`:
`ε_{a,b} → 0` since every nonempty connected polymer `P` contributes a factor
`tanh(a)^|P| → 0` (`|P| ≥ 1`), and `A_C(a) = ∑_P |tanh a|^|P| → 0` likewise, so
`e·A_C(a) < 1`.  Field mirror of `mayer_identity_general_t_eventually`. -/
theorem field_mayer_identity_general_eventually (G : SimpleGraph ι) [Fintype G.edgeSet]
    (b : ℝ) :
    ∀ᶠ a : ℝ in nhds 0,
      fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b := by
  classical
  -- `|ε_{a,b}| < 1` eventually.
  have hε0 : (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, fieldPolymerWeight (0 : ℝ) b P) = 0 := by
    refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
    rw [Finset.mem_erase] at hΓ
    obtain ⟨hne, hin⟩ := hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [mem_vdConnectedPolymerFamilies] at hin
    have hpos : 0 < P.card :=
      (mem_allConnectedPolymers.mp (hin.1 hP)).nonempty.card_pos
    refine Finset.prod_eq_zero hP ?_
    rw [fieldPolymerWeight, Real.tanh_zero, zero_pow hpos.ne', zero_mul]
  have hε_cont : Continuous (fun a : ℝ =>
      ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a b P) := by
    refine continuous_finset_sum _ (fun Γ _ => continuous_finset_prod _ (fun P _ => ?_))
    simp only [fieldPolymerWeight]
    exact (continuous_real_tanh.pow _).mul continuous_const
  have h_abs_ev : ∀ᶠ a : ℝ in nhds 0,
      |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1 := by
    have h := (continuous_abs.comp hε_cont).tendsto 0
    rw [Function.comp_apply, hε0, abs_zero] at h
    exact h.eventually_lt_const zero_lt_one
  -- `e·A_C(a) < 1` eventually.
  have hA0 : Real.exp 1 * ∑ P ∈ allConnectedPolymers G, |Real.tanh (0 : ℝ)| ^ P.card = 0 :=
    mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun P hP => by
      rw [Real.tanh_zero, abs_zero,
        zero_pow (Finset.card_ne_zero.mpr (mem_allConnectedPolymers.mp hP).nonempty)])))
  have hA_cont : Continuous
      (fun a : ℝ => Real.exp 1 * ∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) :=
    continuous_const.mul
      (continuous_finset_sum _ (fun P _ => (continuous_abs.comp continuous_real_tanh).pow P.card))
  have hact_ev : ∀ᶠ a : ℝ in nhds 0,
      Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1 := by
    have h := hA_cont.tendsto 0
    rw [hA0] at h
    exact h.eventually_lt_const zero_lt_one
  exact (h_abs_ev.and hact_ev).mono
    (fun a ha => field_mayer_identity_general G ha.1 ha.2)

end IsingModel
