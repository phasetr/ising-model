import IsingModel.ClusterExpansion.FixedVertexChainMid.TailInductionCompleteTree
import IsingModel.ClusterExpansion.FixedVertexChainEnds

/-!
# Fixed-vertex middle chain (3/3): Penrose tree Fubini and the per-order geometric bound

Structural split (3/3) of `FixedVertexChainMid`.  This child holds the root-filtered Fubini
swap of the Penrose tree sum, its combination with the complete-tree peel bound, and the
headline fixed-root per-order geometric bound
`fixedVertexGasRoot_termAbsSum_succ_le_div_mul_geometric`.  It builds on the complete-tree
bound in the sibling `...TailInductionCompleteTree` and on the bookend clones in
`FixedVertexChainEnds`.  See the `FixedVertexChainMid` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Fubini swap of the fixed-root Penrose tree gas sum, retaining the root filter. -/
theorem fixedVertexGasRoot_penroseTreeSum_le_subtype_parentConstraint
    (𝓟 : Finset (Finset (Sym2 ι))) (v : ι) (n : ℕ)
    (W : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ) (hW : ∀ ω, 0 ≤ W ω) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
              (fun ω => v ∈ polymerSupport (ω 0))).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))), W ω := by
  classical
  set P := (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
    (fun ω => v ∈ polymerSupport (ω 0)) with hP
  have hinner : ∀ ω, (∑ _T ∈ Penrose.spanningTreeEdgeSubsets
        (polymerSeqIncompatibilityGraph ω), W ω)
      = ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
            W ω else 0) := by
    intro ω
    rw [Finset.sum_coe_sort
      (Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1))))
      (fun S => if S ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
        W ω else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Penrose.spanningTreeEdgeSubsets_mono le_top)]
  calc
    (∑ ω ∈ P,
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
        = ∑ ω ∈ P, ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets
              (⊤ : SimpleGraph (Fin (n + 1)))},
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_congr rfl fun ω _ => hinner ω
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P,
            (if T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω) then
              W ω else 0) := Finset.sum_comm
    _ = ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω =>
            T.1 ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω)), W ω :=
          Finset.sum_congr rfl fun T _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ T : {S // S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ P.filter (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
            (ω (Penrose.completeGraphTreeParentCode n T i))), W ω :=
          Finset.sum_le_sum fun T _ =>
            sum_filter_treeIncompat_le_filter_parentConstraint n T P W hW

/-- Fubini swap of the fixed-root Penrose tree sum, retaining the root filter.  Even-gas
instance of `fixedVertexGasRoot_penroseTreeSum_le_subtype_parentConstraint`. -/
theorem fixedVertexRoot_penroseTreeSum_le_subtype_parentConstraint
    (G : SimpleGraph ι) [Fintype G.edgeSet] (v : ι) (n : ℕ)
    (W : (Fin (n + 1) → Finset (Sym2 ι)) → ℝ) (hW : ∀ ω, 0 ≤ W ω) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω), W ω)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => v ∈ polymerSupport (ω 0))).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))), W ω :=
  fixedVertexGasRoot_penroseTreeSum_le_subtype_parentConstraint (allPolymers G) v n W hW

/-- The fixed-root Penrose tree gas sum is bounded by the weighted fixed-root gas peel
bound. -/
theorem fixedVertexGasRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) {c : ℝ} (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (v : ι) (n : ℕ)
    {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
          |t| ^ (ω 0).card
            * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
              * |t| ^ (ω (Fin.succ i)).card)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * fixedVertexRootedGasParentActivePeelBound G 𝓟 c v
                (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
                (fun _ => 0) t := by
  have hWle : ∀ ω : Fin (n + 1) → Finset (Sym2 ι),
      |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
            * |t| ^ (ω (Fin.succ i)).card
        ≤ ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card := by
    intro ω
    rw [Fin.prod_univ_succ,
      Finset.prod_congr rfl
        (g := fun i : Fin n => (Real.exp 1 * |t|) ^ (ω (Fin.succ i)).card)
        fun i _ => (mul_pow _ _ _).symm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (abs_nonneg t) ?_ _
    exact le_mul_of_one_le_left (abs_nonneg t) (Real.one_le_exp_iff.mpr zero_le_one)
  refine (fixedVertexGasRoot_penroseTreeSum_le_subtype_parentConstraint 𝓟 v n
    (fun ω => |t| ^ (ω 0).card
      * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
        * |t| ^ (ω (Fin.succ i)).card)
    (fun ω => by positivity)).trans ?_
  refine Finset.sum_le_sum fun T _ => ?_
  calc
    (∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
        (fun ω => v ∈ polymerSupport (ω 0))).filter
        (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
          (ω (Penrose.completeGraphTreeParentCode n T i))),
        |t| ^ (ω 0).card
          * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
            * |t| ^ (ω (Fin.succ i)).card)
        ≤ ∑ ω ∈ ((Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
            (fun ω => v ∈ polymerSupport (ω 0))).filter
            (fun ω => ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i))),
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card :=
          Finset.sum_le_sum fun ω _ => hWle ω
    _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
            (fun ω => v ∈ polymerSupport (ω 0)),
          if ∀ i : Fin n, PolymersIncompatible (ω (Fin.succ i))
              (ω (Penrose.completeGraphTreeParentCode n T i)) then
            ∏ v : Fin (n + 1), (Real.exp 1 * |t|) ^ (ω v).card
          else 0 := by
          rw [Finset.sum_filter]
    _ = fixedVertexRootedGasParentActiveSum G 𝓟 v (Penrose.completeGraphTreeParentCode n T)
          (Finset.univ : Finset (Fin n))
          (rootedParentActiveClosed_univ (Penrose.completeGraphTreeParentCode n T))
          (fun _ => 0) t :=
          (fixedVertexRootedGasParentActiveSum_univ_zero_eq G 𝓟 v
            (Penrose.completeGraphTreeParentCode n T) t).symm
    _ ≤ ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * fixedVertexRootedGasParentActivePeelBound G 𝓟 c v
              (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t := by
      exact
        fixedVertexRootedGasParentActiveSum_completeTree_univ_zero_le_pow_mul_peelBound
          G hgas hc hsupp v n T hkp

/-- The fixed-root Penrose tree sum is bounded by the weighted fixed-root peel bound.
Even-gas (`c = 1`) instance of
`fixedVertexGasRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound`. -/
theorem fixedVertexRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        ∑ _T ∈ Penrose.spanningTreeEdgeSubsets (polymerSeqIncompatibilityGraph ω),
          |t| ^ (ω 0).card
            * ∏ i : Fin n, Real.exp 1 ^ (ω (Fin.succ i)).card
              * |t| ^ (ω (Fin.succ i)).card)
      ≤ ∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
            S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
          ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
            * fixedVertexRootedParentActivePeelBound G v
                (Penrose.completeGraphTreeParentCode n T) (Finset.univ : Finset (Fin n))
                (fun _ => 0) t := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  simpa [fixedVertexRootedParentActivePeelBound] using
    fixedVertexGasRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound G (evenPolymerGasData G)
      zero_le_one hsupp v n hkp

/-- Fixed-root per-order geometric bound for the root-at-`0` term-absolute gas sum. -/
theorem fixedVertexGasRoot_termAbsSum_succ_le_div_mul_geometric
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {𝓟 : Finset (Finset (Sym2 ι))} (hgas : PolymerGasData G 𝓟) {c : ℝ} (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ 𝓟, ((polymerSupport P).card : ℝ) ≤ c * (P.card : ℝ)) (v : ι) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => 𝓟)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
        * (4 * c * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  refine (fixedVertexGasRoot_termAbsSum_succ_le_treeSum_rootedExpActivity 𝓟 v n ht).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (fixedVertexGasRoot_penroseTreeSum_le_sum_pow_fixedVertexPeelBound G hgas hc hsupp v n hkp)
    (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (sum_pow_fixedVertexRootedGasParentActivePeelBound_le G hgas c hc v n hkp)
    (by positivity)).trans ?_
  have hfact : ((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hq2 : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by
    rw [pow_succ, pow_mul]
  have hgoal_nonneg : (0 : ℝ) ≤ (1 / q) * (4 * c * rr / q ^ 2) ^ n := by positivity
  have hLHS : ((n + 1).factorial : ℝ)⁻¹
        * ((rr ^ n * c ^ n * (4 : ℝ) ^ n * (n.factorial : ℝ)) / q ^ (2 * n + 1))
      = (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
          * ((1 : ℝ) / q * (4 * c * rr / q ^ 2) ^ n) := by
    rw [div_pow, mul_pow, mul_pow, hq2]
    field_simp
    ring
  rw [hLHS]
  calc
    (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
        * ((1 : ℝ) / q * (4 * c * rr / q ^ 2) ^ n)
        ≤ 1 * ((1 : ℝ) / q * (4 * c * rr / q ^ 2) ^ n) :=
          mul_le_mul_of_nonneg_right hfact hgoal_nonneg
    _ = (1 : ℝ) / q * (4 * c * rr / q ^ 2) ^ n := one_mul _

/-- Fixed-root per-order geometric bound for the root-at-`0` term-absolute sum.  Even-gas
(`c = 1`) instance of `fixedVertexGasRoot_termAbsSum_succ_le_div_mul_geometric`. -/
theorem fixedVertexRoot_termAbsSum_succ_le_div_mul_geometric
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => v ∈ polymerSupport (ω 0)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
        * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n := by
  have hsupp : ∀ P ∈ allPolymers G, ((polymerSupport P).card : ℝ) ≤ 1 * (P.card : ℝ) := by
    intro P hP
    rw [one_mul]; exact_mod_cast polymerSupport_card_le_card_of_mem_allPolymers G hP
  have h := fixedVertexGasRoot_termAbsSum_succ_le_div_mul_geometric G (evenPolymerGasData G)
    zero_le_one hsupp v n ht hkp
  simpa using h

end IsingModel
