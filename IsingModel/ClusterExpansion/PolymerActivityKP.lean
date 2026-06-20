import IsingModel.ClusterExpansion.PolymerActivity
import IsingModel.ClusterExpansion.Incompatibility

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

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~378--386.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.7.1
  (Kotecky--Preiss criterion).
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

end IsingModel
