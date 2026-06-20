import IsingModel.ClusterExpansion.PolymerActivityKPMoment
import IsingModel.ClusterExpansion.PolymerActivityTailMoment

/-!
# Sharpened (tail) incompatibility-neighbourhood moment bound (GJ §18.5)

The incompatibility-neighbourhood moment bound (`incompatibilityActivity_cardPow_expWeighted_le`,
#4102) bounds `∑_{Q ∼ P} |Q|^d (e|t|)^{|Q|} ≤ |P|·d!/(1−Δ²e|t|)^{d+1}`.  Replacing the
per-vertex moment bound by its tail sharpening (`rootedPolymerActivity_cardPow_tail_le`,
#4121) — valid because every incompatible polymer is nonempty — carries an extra factor
`Δ²e|t|`:

`∑_{Q ∼ P} |Q|^d (e|t|)^{|Q|} ≤ |P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.

* `incompatibilityActivity_cardPow_expWeighted_tail_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharpened (tail) incompatibility-neighbourhood moment bound.**  For
`P ∈ allPolymers G` and `Δ²e|t| < 1`, the `d`-th moment of the `e`-weighted activity of
the polymers incompatible with `P` carries an extra factor `Δ²e|t|` over
`incompatibilityActivity_cardPow_expWeighted_le`:
`∑_{Q ∼ P} |Q|^d (e|t|)^{|Q|} ≤ |P|·(Δ²e|t|)·d!/(1−Δ²e|t|)^{d+1}`.  The reduction to the
per-vertex moment sums (each incompatible polymer rooted at a shared support vertex) is
as in #4102; the per-vertex sums are then bounded by the tail moment bound #4121. -/
theorem incompatibilityActivity_cardPow_expWeighted_tail_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {P : Finset (Sym2 ι)}
    (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ Q ∈ incompatiblePolymers G P,
        (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
      ≤ (P.card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
  have hw0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  -- Reduce to the per-support-vertex moment sums (identical to #4102).
  have key : (∑ Q ∈ incompatiblePolymers G P,
        (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ v ∈ polymerSupport P,
          ∑ Q ∈ rootedPolymers G v,
            (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card := by
    calc (∑ Q ∈ incompatiblePolymers G P,
            (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
        ≤ ∑ Q ∈ incompatiblePolymers G P,
            ∑ _v ∈ (polymerSupport P).filter (· ∈ polymerSupport Q),
              (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          rw [Finset.sum_const, incompatiblePolymers, Finset.mem_filter] at *
          obtain ⟨v, hvP, hvQ⟩ :=
            PolymersIncompatible.iff_exists_shared_vertex.mp hQ.2
          have hne : ((polymerSupport P).filter (· ∈ polymerSupport Q)).Nonempty :=
            ⟨v, Finset.mem_filter.mpr ⟨hvP, hvQ⟩⟩
          have h1 : (1 : ℝ)
              ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ) := by
            exact_mod_cast hne.card_pos
          calc (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card
              = 1 * ((Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card) := (one_mul _).symm
            _ ≤ (((polymerSupport P).filter (· ∈ polymerSupport Q)).card : ℝ)
                  * ((Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ((polymerSupport P).filter (· ∈ polymerSupport Q)).card
                  • ((Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card) := (nsmul_eq_mul _ _).symm
      _ = ∑ Q ∈ incompatiblePolymers G P,
            ∑ v ∈ polymerSupport P,
              (if v ∈ polymerSupport Q then
                (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card else 0) := by
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [Finset.sum_filter]
      _ = ∑ v ∈ polymerSupport P,
            ∑ Q ∈ incompatiblePolymers G P,
              (if v ∈ polymerSupport Q then
                (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card else 0) :=
          Finset.sum_comm
      _ ≤ ∑ v ∈ polymerSupport P,
            ∑ Q ∈ rootedPolymers G v,
              (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro Q hQ
            rw [Finset.mem_filter, incompatiblePolymers, Finset.mem_filter] at hQ
            rw [rootedPolymers, Finset.mem_filter]
            exact ⟨hQ.1.1, hQ.2⟩
          · intro Q _ _; positivity
  refine key.trans ?_
  calc (∑ v ∈ polymerSupport P,
          ∑ Q ∈ rootedPolymers G v, (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ _v ∈ polymerSupport P,
          (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact rootedPolymerActivity_cardPow_tail_le G v d hw0 hkp
    _ = ((polymerSupport P).card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (P.card : ℝ)
          * (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            * ((d.factorial : ℝ)
                / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1))) := by
        have hpos : (0 : ℝ) < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by linarith
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (by positivity)
            (div_nonneg (by positivity) (le_of_lt (pow_pos hpos (d + 1)))))
        exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP

end IsingModel
