import IsingModel.ClusterExpansion.PolymerActivityKP
import IsingModel.ClusterExpansion.PolymerActivityMoment

/-!
# Incompatibility-neighbourhood moment bound (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction discharges a leaf into its
parent, and when the leaf has already absorbed `d` of its own children it carries a
polynomial-moment factor `|Q|^d`.  The moment generalisation of the
Kotecky--Preiss neighbourhood bound (`incompatibilityActivity_expWeighted_le`,
combined with the per-vertex moment bound `rootedPolymerActivity_cardPow_le`) is:
for `P ∈ allPolymers G` and `Δ²·e·|t| < 1` (`Δ = G.maxDegree`),
`∑_{Q ∼ P} |Q|^d (e|t|)^{|Q|} ≤ |P|·d!·(1 − Δ²e|t|)^{-(d+1)}`.

The `d = 0` case is `incompatibilityActivity_expWeighted_le` (up to `|supp P| ≤ |P|`).

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Incompatibility-neighbourhood moment bound.**  For `P ∈ allPolymers G` and
`Δ²·e·|t| < 1`, the `d`-th moment of the `e`-weighted activity of the polymers
incompatible with `P` is bounded by `|P|·d!·(1 − Δ²e|t|)^{-(d+1)}`:
`∑_{Q ∼ P} |Q|^d (e|t|)^{|Q|} ≤ |P|·d!/(1 − Δ²e|t|)^{d+1}`.  Each incompatible polymer
is rooted at one of the `|supp P| ≤ |P|` support vertices of `P`, and the per-vertex
sum is the moment bound `rootedPolymerActivity_cardPow_le`. -/
theorem incompatibilityActivity_cardPow_expWeighted_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {P : Finset (Sym2 ι)}
    (hP : P ∈ allPolymers G) (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ Q ∈ incompatiblePolymers G P,
        (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
      ≤ (P.card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
  have hw0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
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
          ((d.factorial : ℝ)
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact rootedPolymerActivity_cardPow_le G v d hw0 hkp
    _ = ((polymerSupport P).card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (P.card : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
        have hpos : (0 : ℝ) < 1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by
          linarith
        refine mul_le_mul_of_nonneg_right ?_
          (div_nonneg (by positivity) (le_of_lt (pow_pos hpos (d + 1))))
        exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP

end IsingModel
