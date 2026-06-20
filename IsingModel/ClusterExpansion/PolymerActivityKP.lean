import IsingModel.ClusterExpansion.PolymerActivity
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.Conditioning.EdgeSetHandshake

/-!
# Weighted per-vertex and incompatibility-neighbourhood activity bounds (GJ §18.5)

The Kotecky--Preiss convergence criterion for the cluster expansion is a *local*
(per-vertex) condition on the *weighted* polymer activity `∑_{P∋v} |w(P)| e^{|P|}`.
This file provides the two volume-uniform local inputs built on the per-vertex
activity bound of `PolymerActivity`:

* `rootedPolymerActivity_expWeighted_le_geometric`: the per-vertex
  `e`-weighted activity `∑_{Q ∋ v} (e·|t|)^{|Q|} ≤ (1 − Δ²·e·|t|)⁻¹` under
  `Δ²·e·|t| < 1` (a substitution `t ↦ e·|t|` in `rootedPolymerActivity_le_geometric`).
* `incompatibilityActivity_expWeighted_le`: the activity of the polymers
  *incompatible* with a fixed polymer `P` (those sharing a support vertex) is at
  most `|supp P|·(1 − Δ²·e·|t|)⁻¹`.  Each incompatible polymer is rooted at one of
  the `|supp P|` vertices of `P`, so the incompatibility neighbourhood activity is
  controlled by `|supp P|` copies of the per-vertex geometric bound.

This `∑_{Q ∼ P} (e·|t|)^{|Q|} ≤ |supp P|·(1 − Δ²e|t|)⁻¹` estimate is the direct
input to the Kotecky--Preiss / rooted-cluster tree induction; both bounds depend
only on the maximum degree, **not** on the volume.

Sharpening to the *tail* geometric series `Δ²e|t|·(1 − Δ²e|t|)⁻¹` (polymers are
nonempty, so the activity sum starts at edge-count `1`) and using the handshake
bound `|supp P| ≤ |P|` for even subgraphs (every support vertex has even degree
`≥ 2`) discharges the **Kotecky--Preiss hypothesis** (FV Theorem 5.4) with the
weight `a(P) = |P|` in the high-temperature regime `Δ²e|t| ≤ ½`:
`incompatibilityActivity_expWeighted_le_card_of_half` gives
`∑_{Q ∼ P} (e|t|)^{|Q|} ≤ |P|`, the exact volume-uniform input that a
Kotecky--Preiss convergence theorem consumes.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion); §5.7.1 for the Ising
  polymer application.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Per-vertex `e`-weighted activity bound (Kotecky--Preiss input).**  For
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), the `e`-weighted polymer activity through `v`
satisfies `∑_{Q ∋ v} (e^{|Q|})·|t|^{|Q|} ≤ (1 − Δ²·e·|t|)⁻¹`. -/
theorem rootedPolymerActivity_expWeighted_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ Q ∈ rootedPolymers G v, Real.exp 1 ^ Q.card * |t| ^ Q.card)
      ≤ (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))⁻¹ := by
  have h0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  have hgeo := rootedPolymerActivity_le_geometric G v h0 hkp
  rw [rootedPolymerActivity] at hgeo
  refine le_trans (le_of_eq ?_) hgeo
  exact Finset.sum_congr rfl fun Q _ => (mul_pow _ _ _).symm

/-- The polymers of `G` that are incompatible with `P` (i.e. share a support
vertex with `P`). -/
noncomputable def incompatiblePolymers (G : SimpleGraph ι) [Fintype G.edgeSet]
    (P : Finset (Sym2 ι)) : Finset (Finset (Sym2 ι)) :=
  (allPolymers G).filter (PolymersIncompatible P)

/-- **Incompatibility-neighbourhood activity bound (Kotecky--Preiss input).**  For
`Δ²·e·|t| < 1` (`Δ = G.maxDegree`), the total `e`-weighted activity of the polymers
incompatible with `P` is at most `|supp P|·(1 − Δ²·e·|t|)⁻¹`.  Each incompatible
polymer is rooted at one of the `|supp P|` support vertices of `P`, so the
neighbourhood activity is bounded by `|supp P|` copies of the per-vertex geometric
bound. -/
theorem incompatibilityActivity_expWeighted_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (P : Finset (Sym2 ι)) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card)
      ≤ ((polymerSupport P).card : ℝ)
          * (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))⁻¹ := by
  have hw0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  -- Each incompatible polymer is counted at least once when ranging over the
  -- shared support vertices of `P`.
  have key : (∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ v ∈ polymerSupport P,
          ∑ Q ∈ rootedPolymers G v, (Real.exp 1 * |t|) ^ Q.card := by
    calc (∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card)
        ≤ ∑ Q ∈ incompatiblePolymers G P,
            ∑ _v ∈ (polymerSupport P).filter (· ∈ polymerSupport Q),
              (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          rw [Finset.sum_const, incompatiblePolymers, Finset.mem_filter] at *
          obtain ⟨v, hvP, hvQ⟩ :=
            PolymersIncompatible.iff_exists_shared_vertex.mp hQ.2
          have hne : ((polymerSupport P).filter (· ∈ polymerSupport Q)).Nonempty :=
            ⟨v, Finset.mem_filter.mpr ⟨hvP, hvQ⟩⟩
          have h1 : (1 : ℝ)
              ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ) := by
            exact_mod_cast hne.card_pos
          calc (Real.exp 1 * |t|) ^ Q.card = 1 * (Real.exp 1 * |t|) ^ Q.card :=
                (one_mul _).symm
            _ ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ)
                  * (Real.exp 1 * |t|) ^ Q.card :=
                mul_le_mul_of_nonneg_right h1 (pow_nonneg hw0 _)
            _ = ((polymerSupport P).filter (· ∈ polymerSupport Q)).card
                  • (Real.exp 1 * |t|) ^ Q.card := (nsmul_eq_mul _ _).symm
      _ = ∑ Q ∈ incompatiblePolymers G P,
            ∑ v ∈ polymerSupport P,
              (if v ∈ polymerSupport Q then (Real.exp 1 * |t|) ^ Q.card else 0) := by
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ v ∈ polymerSupport P,
            ∑ Q ∈ incompatiblePolymers G P,
              (if v ∈ polymerSupport Q then (Real.exp 1 * |t|) ^ Q.card else 0) :=
          Finset.sum_comm
      _ ≤ ∑ v ∈ polymerSupport P,
            ∑ Q ∈ rootedPolymers G v, (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro Q hQ
            rw [Finset.mem_filter, incompatiblePolymers, Finset.mem_filter] at hQ
            rw [rootedPolymers, Finset.mem_filter]
            exact ⟨hQ.1.1, hQ.2⟩
          · intro Q _ _; exact pow_nonneg hw0 _
  refine key.trans ?_
  calc (∑ v ∈ polymerSupport P,
          ∑ Q ∈ rootedPolymers G v, (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ _v ∈ polymerSupport P,
          (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))⁻¹ := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hgeo := rootedPolymerActivity_le_geometric G v hw0 hkp
        rwa [rootedPolymerActivity] at hgeo
    _ = ((polymerSupport P).card : ℝ)
          * (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Tail per-vertex activity bound.**  Polymers are nonempty (edge-count `≥ 1`),
so the per-vertex activity is bounded by the *tail* geometric series:
`∑_{Q ∋ v} u^{|Q|} ≤ (Δ²u)·(1 − Δ²u)⁻¹` for `0 ≤ u`, `Δ²u < 1`.  Unlike the full
geometric bound `(1 − Δ²u)⁻¹`, this tail vanishes as `u → 0`, which is what the
Kotecky--Preiss criterion requires. -/
theorem rootedPolymerActivity_le_geometric_tail (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (G.maxDegree : ℝ) ^ 2 * u < 1) :
    rootedPolymerActivity G v u
      ≤ (G.maxDegree : ℝ) ^ 2 * u * (1 - (G.maxDegree : ℝ) ^ 2 * u)⁻¹ := by
  set r : ℝ := (G.maxDegree : ℝ) ^ 2 * u with hr
  have hr0 : (0 : ℝ) ≤ r := mul_nonneg (by positivity) hu0
  have hmaps : ∀ P ∈ rootedPolymers G v, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    rw [rootedPolymers, Finset.mem_filter] at hP
    have hsub : P ⊆ G.edgeFinset := (mem_allPolymers.mp hP.1).isEven.subset
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card hsub))
  rw [rootedPolymerActivity,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun P => u ^ P.card)]
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), u ^ P.card)
        ≤ (if ℓ = 0 then 0 else r ^ ℓ) := by
    intro ℓ _
    rcases eq_or_ne ℓ 0 with rfl | hℓ
    · have hempty : (rootedPolymers G v).filter (fun P => P.card = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro P hP hP0
        rw [rootedPolymers, Finset.mem_filter] at hP
        exact absurd (Finset.card_eq_zero.mp hP0)
          (Finset.nonempty_iff_ne_empty.mp (mem_allPolymers.mp hP.1).nonempty)
      rw [hempty, Finset.sum_empty]
      exact le_of_eq (if_pos rfl).symm
    · rw [if_neg hℓ]
      have hconst : (∑ P ∈ (rootedPolymers G v).filter (fun P => P.card = ℓ), u ^ P.card)
          = ((rootedPolymersOfCard G v ℓ).card : ℝ) * u ^ ℓ := by
        rw [rootedPolymersOfCard]
        rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2]]
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst]
      have hcount : ((rootedPolymersOfCard G v ℓ).card : ℝ) ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) := by
        exact_mod_cast rootedPolymersOfCard_card_le_maxDegree_pow G v ℓ
      calc ((rootedPolymersOfCard G v ℓ).card : ℝ) * u ^ ℓ
          ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) * u ^ ℓ :=
            mul_le_mul_of_nonneg_right hcount (pow_nonneg hu0 ℓ)
        _ = r ^ ℓ := by rw [hr, mul_pow, pow_mul]
  have hsummable : Summable (fun ℓ : ℕ => if ℓ = 0 then (0 : ℝ) else r ^ ℓ) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
      (summable_geometric_of_lt_one hr0 hu)
    · split <;> positivity
    · split
      · exact pow_nonneg hr0 ℓ
      · exact le_refl _
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  refine le_trans (hsummable.sum_le_tsum (Finset.range _) (fun ℓ _ => ?_)) ?_
  · split <;> positivity
  · have htsum : (∑' ℓ : ℕ, (if ℓ = 0 then (0 : ℝ) else r ^ ℓ)) = r * (1 - r)⁻¹ := by
      rw [hsummable.tsum_eq_zero_add]
      have hfun : ∀ n : ℕ, (if n + 1 = 0 then (0 : ℝ) else r ^ (n + 1)) = r * r ^ n := by
        intro n; rw [if_neg (Nat.add_one_ne_zero n), pow_succ']
      rw [if_pos rfl, zero_add, tsum_congr hfun, tsum_mul_left,
        tsum_geometric_of_lt_one hr0 hu]
    rw [htsum]

/-- **A polymer has at most as many support vertices as edges.**  In an even
subgraph every support vertex has even degree `≥ 2`, so by the handshake identity
`2·|supp P| ≤ ∑_v deg_P(v) = 2·|P|`. -/
theorem polymerSupport_card_le_card_of_mem_allPolymers (G : SimpleGraph ι)
    [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : P ∈ allPolymers G) :
    (polymerSupport P).card ≤ P.card := by
  have hpoly := mem_allPolymers.mp hP
  have hhand : ∑ v : ι, (P.filter (v ∈ ·)).card = 2 * P.card :=
    sum_filter_card_eq_two_mul_card G P hpoly.isEven.subset
  have hdeg : ∀ v ∈ polymerSupport P, 2 ≤ (P.filter (v ∈ ·)).card := by
    intro v hv
    obtain ⟨k, hk⟩ := hpoly.isEven.even_degree v
    obtain ⟨e, heP, hve⟩ := mem_polymerSupport.mp hv
    have hpos : 0 < (P.filter (v ∈ ·)).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heP, hve⟩⟩
    omega
  have hsumeq : ∑ v : ι, (P.filter (v ∈ ·)).card
      = ∑ v ∈ polymerSupport P, (P.filter (v ∈ ·)).card := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro v _ hv
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e heP hve
    exact hv (mem_polymerSupport.mpr ⟨e, heP, hve⟩)
  have hlb : 2 * (polymerSupport P).card
      ≤ ∑ v ∈ polymerSupport P, (P.filter (v ∈ ·)).card := by
    calc 2 * (polymerSupport P).card = ∑ _v ∈ polymerSupport P, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ polymerSupport P, (P.filter (v ∈ ·)).card := Finset.sum_le_sum hdeg
  omega

/-- **Kotecky--Preiss hypothesis discharged at high temperature** (FV Theorem 5.4,
weight `a(P) = |P|`).  For `Δ²·e·|t| ≤ ½` (`Δ = G.maxDegree`), the total
`e`-weighted activity of the polymers incompatible with `P` is at most `|P|`:
`∑_{Q ∼ P} e^{|Q|}·|t|^{|Q|} ≤ |P|`.  This is the exact volume-uniform input that a
Kotecky--Preiss cluster-expansion convergence theorem consumes.  The proof uses the
tail per-vertex bound `Δ²e|t|·(1 − Δ²e|t|)⁻¹ ≤ 1` (valid for `Δ²e|t| ≤ ½`) summed
over the `|supp P| ≤ |P|` support vertices of `P`. -/
theorem incompatibilityActivity_expWeighted_le_card_of_half (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {P : Finset (Sym2 ι)}
    (hP : P ∈ allPolymers G) {t : ℝ}
    (hsmall : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) ≤ (1 / 2 : ℝ)) :
    (∑ Q ∈ incompatiblePolymers G P, Real.exp 1 ^ Q.card * |t| ^ Q.card)
      ≤ (P.card : ℝ) := by
  set r : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrdef
  have hu0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  have hr0 : (0 : ℝ) ≤ r := mul_nonneg (by positivity) hu0
  have hr1 : r < 1 := lt_of_le_of_lt hsmall (by norm_num)
  have hrw : (∑ Q ∈ incompatiblePolymers G P, Real.exp 1 ^ Q.card * |t| ^ Q.card)
      = ∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card :=
    Finset.sum_congr rfl fun Q _ => (mul_pow _ _ _).symm
  rw [hrw]
  -- bound by the support sum of the tail per-vertex activity
  have hkey : (∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ v ∈ polymerSupport P, rootedPolymerActivity G v (Real.exp 1 * |t|) := by
    simp only [rootedPolymerActivity]
    calc (∑ Q ∈ incompatiblePolymers G P, (Real.exp 1 * |t|) ^ Q.card)
        ≤ ∑ Q ∈ incompatiblePolymers G P,
            ∑ _v ∈ (polymerSupport P).filter (· ∈ polymerSupport Q),
              (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          rw [Finset.sum_const, incompatiblePolymers, Finset.mem_filter] at *
          obtain ⟨v, hvP, hvQ⟩ :=
            PolymersIncompatible.iff_exists_shared_vertex.mp hQ.2
          have hne : ((polymerSupport P).filter (· ∈ polymerSupport Q)).Nonempty :=
            ⟨v, Finset.mem_filter.mpr ⟨hvP, hvQ⟩⟩
          have h1 : (1 : ℝ)
              ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ) := by
            exact_mod_cast hne.card_pos
          calc (Real.exp 1 * |t|) ^ Q.card = 1 * (Real.exp 1 * |t|) ^ Q.card :=
                (one_mul _).symm
            _ ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ)
                  * (Real.exp 1 * |t|) ^ Q.card :=
                mul_le_mul_of_nonneg_right h1 (pow_nonneg hu0 _)
            _ = ((polymerSupport P).filter (· ∈ polymerSupport Q)).card
                  • (Real.exp 1 * |t|) ^ Q.card := (nsmul_eq_mul _ _).symm
      _ = ∑ Q ∈ incompatiblePolymers G P,
            ∑ v ∈ polymerSupport P,
              (if v ∈ polymerSupport Q then (Real.exp 1 * |t|) ^ Q.card else 0) := by
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ v ∈ polymerSupport P,
            ∑ Q ∈ incompatiblePolymers G P,
              (if v ∈ polymerSupport Q then (Real.exp 1 * |t|) ^ Q.card else 0) :=
          Finset.sum_comm
      _ ≤ ∑ v ∈ polymerSupport P,
            ∑ Q ∈ rootedPolymers G v, (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro Q hQ
            rw [Finset.mem_filter, incompatiblePolymers, Finset.mem_filter] at hQ
            rw [rootedPolymers, Finset.mem_filter]
            exact ⟨hQ.1.1, hQ.2⟩
          · intro Q _ _; exact pow_nonneg hu0 _
  refine hkey.trans ?_
  -- each per-vertex activity ≤ r·(1−r)⁻¹ ≤ 1, summed over ≤ |P| vertices
  have hfrac : r * (1 - r)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hsupp : ((polymerSupport P).card : ℝ) ≤ (P.card : ℝ) := by
    exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  calc (∑ v ∈ polymerSupport P, rootedPolymerActivity G v (Real.exp 1 * |t|))
      ≤ ∑ _v ∈ polymerSupport P, r * (1 - r)⁻¹ := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact rootedPolymerActivity_le_geometric_tail G v hu0 hr1
    _ = ((polymerSupport P).card : ℝ) * (r * (1 - r)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((polymerSupport P).card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = ((polymerSupport P).card : ℝ) := mul_one _
    _ ≤ (P.card : ℝ) := hsupp

end IsingModel
