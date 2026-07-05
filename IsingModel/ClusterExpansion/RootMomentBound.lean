import IsingModel.ClusterExpansion.PolymerActivityMoment

/-!
# The root moment bound (GJ §18.5)

In the leaf-peel child-count peel bound the root vertex carries the moment sum
`∑_{P ∈ allPolymers G} |P|^d (e|t|)^{|P|}` (the base case of the leaf-peel recursion).
Bounding this requires summing the per-vertex moment bound over the vertices: since every
polymer is rooted at each of its `|supp P| ≥ 1` support vertices,

`∑_{P ∈ allPolymers G} |P|^d (e|t|)^{|P|} ≤ |V|·d!/(1−Δ²e|t|)^{d+1}`,

where `|V| = Fintype.card ι`.

* `sum_allPolymers_cardPow_expWeighted_le`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A nonempty polymer has nonempty support.**  Since a nonempty edge set contains an
edge and every edge contains a vertex, the support cardinality is at least one. -/
theorem one_le_card_polymerSupport_of_nonempty {P : Finset (Sym2 ι)} (hP : P.Nonempty) :
    1 ≤ (polymerSupport P).card := by
  obtain ⟨e, he⟩ := hP
  refine Finset.card_pos.mpr ?_
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, mem_polymerSupport.mpr ⟨_, he, Sym2.mem_mk_left a b⟩⟩

omit [DecidableEq ι] in
/-- **The root moment bound over an abstract gas.**  For `Δ²e|t| < 1`, the `d`-th moment
of the `e`-weighted activity summed over all polymers of the gas `𝓟` is at most
`|V|·d!/(1−Δ²e|t|)^{d+1}`.  Every polymer is rooted at each of its `|supp P| ≥ 1` support
vertices (nonemptiness from `PolymerGasData`), so the sum over the gas is dominated by the
sum over vertices of the per-vertex moment bound `rootedGasPolymerActivity_cardPow_le`. -/
theorem sum_gasPolymers_cardPow_expWeighted_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟)
    (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ P ∈ 𝓟, (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card)
      ≤ (Fintype.card ι : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
  classical
  have hw0 : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
  -- Cover each polymer by its support vertices (each counted ≥ 1 time).
  have key : (∑ P ∈ 𝓟, (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card)
      ≤ ∑ v : ι, ∑ Q ∈ rootedGasPolymers 𝓟 v,
          (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card := by
    calc (∑ P ∈ 𝓟, (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card)
        ≤ ∑ P ∈ 𝓟,
            ∑ _v ∈ polymerSupport P, (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [Finset.sum_const]
          have h1 : (1 : ℝ) ≤ ((polymerSupport P).card : ℝ) := by
            exact_mod_cast one_le_card_polymerSupport_of_nonempty (hgas.nonempty P hP)
          calc (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card
              = 1 * ((P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card) := (one_mul _).symm
            _ ≤ ((polymerSupport P).card : ℝ)
                  * ((P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (polymerSupport P).card
                  • ((P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card) := (nsmul_eq_mul _ _).symm
      _ = ∑ P ∈ 𝓟,
            ∑ v : ι, (if v ∈ polymerSupport P then
              (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card else 0) := by
          refine Finset.sum_congr rfl fun P _ => ?_
          have hsf := Finset.sum_filter (s := (Finset.univ : Finset ι))
            (· ∈ polymerSupport P)
            (fun _ : ι => (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card)
          rw [Finset.filter_univ_mem] at hsf
          exact hsf
      _ = ∑ v : ι, ∑ P ∈ 𝓟, (if v ∈ polymerSupport P then
              (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card else 0) := Finset.sum_comm
      _ = ∑ v : ι, ∑ Q ∈ rootedGasPolymers 𝓟 v,
            (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [rootedGasPolymers, Finset.sum_filter]
  refine key.trans ?_
  calc (∑ v : ι, ∑ Q ∈ rootedGasPolymers 𝓟 v,
          (Q.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ Q.card)
      ≤ ∑ _v : ι, ((d.factorial : ℝ)
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) :=
        Finset.sum_le_sum fun v _ => rootedGasPolymerActivity_cardPow_le G hgas v d hw0 hkp
    _ = (Fintype.card ι : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The root moment bound.**  For `Δ²e|t| < 1`, the `d`-th moment of the `e`-weighted
activity summed over all polymers of `G` is at most `|V|·d!/(1−Δ²e|t|)^{d+1}`.  Even-gas
instance of `sum_gasPolymers_cardPow_expWeighted_le`. -/
theorem sum_allPolymers_cardPow_expWeighted_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (d : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ P ∈ allPolymers G, (P.card : ℝ) ^ d * (Real.exp 1 * |t|) ^ P.card)
      ≤ (Fintype.card ι : ℝ)
          * ((d.factorial : ℝ)
              / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (d + 1)) :=
  sum_gasPolymers_cardPow_expWeighted_le G (evenPolymerGasData G) d hkp

end IsingModel
