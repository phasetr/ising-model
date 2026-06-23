import IsingModel.ClusterExpansion.FixedVertexTouchingPerOrder
import IsingModel.ClusterExpansion.TouchingClusterDecomp
import IsingModel.ClusterExpansion.MayerCore.TermsComplexPerSiteBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Geometric first-moment sum.**  For `0 ≤ ρ < 1`, the shifted geometric moment satisfies
`∑'_n (n+1)ρ^n = (1-ρ)⁻²`. -/
theorem tsum_nat_succ_mul_geometric_eq_inv_sq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ρ ^ n) = (1 - ρ)⁻¹ ^ 2 := by
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact hρ
  have hn : Summable fun n : ℕ => (n : ℝ) * ρ ^ n :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hg : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρ
  have hsplit : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n)
      = fun n : ℕ => (n : ℝ) * ρ ^ n + ρ ^ n := by
    funext n
    norm_num [Nat.cast_add, add_mul]
  rw [hsplit, hn.tsum_add hg, tsum_coe_mul_geometric_of_norm_lt_one hnorm,
    tsum_geometric_of_lt_one hρ0 hρ]
  have h1 : 1 - ρ ≠ 0 := by linarith
  field_simp [h1]
  ring

/-- **Summability of the fixed-vertex touching majorant.**  The per-order fixed-vertex touching
bound is dominated by `(1-rr)⁻¹ (n+1)ρ^n`, hence is summable when `ρ < 1`. -/
theorem summable_fixedVertexTouching_termAbsSum_succ
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) {t : ℝ}
    (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    Summable fun n : ℕ =>
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
  classical
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set ρ : ℝ := 4 * rr / (1 - rr) ^ 2 with hρdef
  set K : ℝ := 1 / (1 - rr) with hK
  have hρlt : ρ < 1 := by
    rw [hρdef, hrr]
    exact hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    positivity
  have hsuccSumm : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n := by
    have hnorm : ‖ρ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
      exact hρlt
    have hn : Summable fun n : ℕ => (n : ℝ) * ρ ^ n :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hg : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρlt
    have hsplit : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n)
        = fun n : ℕ => (n : ℝ) * ρ ^ n + ρ ^ n := by
      funext n
      norm_num [Nat.cast_add, add_mul]
    rw [hsplit]
    exact hn.add hg
  have hdom : Summable fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) :=
    hsuccSumm.mul_left K
  have hterm : ∀ n : ℕ,
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        ≤ K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) := by
    intro n
    have h := fixedVertexTouching_termAbsSum_succ_le_nat_mul_geometric
      (G := G) (v := v) (n := n) (t := t) ht hkp
    rw [← hrr, ← hρdef, ← hK] at h
    calc
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
          ≤ ((n + 1 : ℕ) : ℝ) * (K * ρ ^ n) := h
      _ = K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) := by ring
  refine Summable.of_nonneg_of_le (fun n => ?_) hterm hdom
  refine Finset.sum_nonneg fun ω _ => ?_
  exact mul_nonneg (abs_nonneg _) (clusterSeqActivity_nonneg ht ω)

/-- **Fixed-vertex touching clusters are summably bounded.**  Summing the per-order fixed-vertex
bound gives the local KP constant `(1-rr)⁻¹(1-ρ)⁻²`, with
`rr = Δ² e |t|` and `ρ = 4rr/(1-rr)²`. -/
theorem fixedVertexTouching_tsum_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) {t : ℝ}
    (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    (∑' n : ℕ,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ ^ 2 := by
  classical
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set ρ : ℝ := 4 * rr / (1 - rr) ^ 2 with hρdef
  set K : ℝ := 1 / (1 - rr) with hK
  have hρlt : ρ < 1 := by
    rw [hρdef, hrr]
    exact hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    positivity
  have hsuccSumm : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n := by
    have hnorm : ‖ρ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
      exact hρlt
    have hn : Summable fun n : ℕ => (n : ℝ) * ρ ^ n :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hg : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρlt
    have hsplit : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n)
        = fun n : ℕ => (n : ℝ) * ρ ^ n + ρ ^ n := by
      funext n
      norm_num [Nat.cast_add, add_mul]
    rw [hsplit]
    exact hn.add hg
  have hdom : Summable fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) :=
    hsuccSumm.mul_left K
  have hterm : ∀ n : ℕ,
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        ≤ K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) := by
    intro n
    have h := fixedVertexTouching_termAbsSum_succ_le_nat_mul_geometric
      (G := G) (v := v) (n := n) (t := t) ht hkp
    rw [← hrr, ← hρdef, ← hK] at h
    calc
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
          ≤ ((n + 1 : ℕ) : ℝ) * (K * ρ ^ n) := h
      _ = K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) := by ring
  have hleft := summable_fixedVertexTouching_termAbsSum_succ G v ht hkp hρ
  calc
    (∑' n : ℕ,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ∑' n : ℕ, K * (((n + 1 : ℕ) : ℝ) * ρ ^ n) :=
        hleft.tsum_le_tsum hterm hdom
    _ = K * (1 - ρ)⁻¹ ^ 2 := by
        rw [tsum_mul_left, tsum_nat_succ_mul_geometric_eq_inv_sq hρ0 hρlt]
    _ = (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ ^ 2 := by
        rw [hK, hρdef, hrr]

open Classical in
/-- **Touching `C` is bounded by a union over the vertices of `polymerSupport C`.**  If a
sequence contains a polymer not vertex-disjoint from `C`, then some vertex of `polymerSupport C`
lies in the support of one of its coordinates. -/
theorem touchingCluster_termAbsSum_le_support_vertex_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
  classical
  set S := Fintype.piFinset (fun _ : Fin n => allPolymers G) with hS
  set a : (Fin n → Finset (Sym2 ι)) → ℝ :=
    fun ω => |ursellCoefficient ω| * clusterSeqActivity t ω with ha
  have hanonneg : ∀ ω, 0 ≤ a ω := by
    intro ω
    exact mul_nonneg (abs_nonneg _) (clusterSeqActivity_nonneg ht ω)
  have hvertexNonneg : ∀ ω, 0 ≤ ∑ v ∈ polymerSupport C,
      if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    intro ω
    refine Finset.sum_nonneg fun v _ => ?_
    split_ifs with h
    · exact hanonneg ω
    · exact le_refl 0
  have hRHS : (∑ v ∈ polymerSupport C,
        ∑ ω ∈ S.filter (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)), a ω)
      = ∑ ω ∈ S, ∑ v ∈ polymerSupport C,
          if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  refine le_trans ?_ (ge_of_eq hRHS)
  refine le_trans (Finset.sum_le_sum (fun ω hω => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => hvertexNonneg ω))
  rw [Finset.mem_filter] at hω
  obtain ⟨i, hi⟩ := hω.2
  have hshared : ∃ v : ι, v ∈ polymerSupport C ∧ v ∈ polymerSupport (ω i) := by
    exact PolymersIncompatible.iff_exists_shared_vertex.mp hi
  obtain ⟨v, hvC, hvω⟩ := hshared
  calc a ω = if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
        rw [if_pos ⟨i, hvω⟩]
    _ ≤ ∑ v ∈ polymerSupport C,
        if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 :=
        Finset.single_le_sum
          (f := fun v => if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0)
          (fun v _ => by
            change (0 : ℝ) ≤ if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0
            split_ifs with h; exacts [hanonneg ω, le_refl 0])
          hvC

/-- **Local KP bound for the Mayer-sum difference caused by avoiding a support.**  On the
high-temperature KP disc, the norm of the difference between the full Mayer sum and the Mayer sum
of `Gavoid G C` is bounded by the fixed-vertex KP constant times `|polymerSupport C|`. -/
theorem norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {t : ℝ} (ht : 0 ≤ t)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    ‖(∑' n : ℕ, mayerExpansionTermComplex G n (t : ℂ))
        - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n (t : ℂ))‖
      ≤ ((1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  set κ : ℝ := (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ ^ 2 with hκ
  obtain ⟨hkpAvoid, hρAvoid⟩ := gavoid_kp_conditions (G := G) (C := C) (R := |t|) hkp hρ
  have hsuccG : Summable fun n : ℕ => ‖mayerExpansionTermComplex G (n + 1) (t : ℂ)‖ := by
    refine summable_norm_mayerExpansionTermComplex_succ_of_tail_condition (G := G) ?_ ?_
    · simpa [Complex.norm_real, Real.norm_eq_abs] using hkp
    · simpa [Complex.norm_real, Real.norm_eq_abs] using hρ
  have hsuccA : Summable fun n : ℕ =>
      ‖mayerExpansionTermComplex (Gavoid G C) (n + 1) (t : ℂ)‖ := by
    refine summable_norm_mayerExpansionTermComplex_succ_of_tail_condition (G := Gavoid G C) ?_ ?_
    · simpa [Complex.norm_real, Real.norm_eq_abs] using hkpAvoid
    · simpa [Complex.norm_real, Real.norm_eq_abs] using hρAvoid
  have hsumG : Summable fun n : ℕ => mayerExpansionTermComplex G n (t : ℂ) :=
    (summable_nat_add_iff 1).mp hsuccG.of_norm
  have hsumA : Summable fun n : ℕ => mayerExpansionTermComplex (Gavoid G C) n (t : ℂ) :=
    (summable_nat_add_iff 1).mp hsuccA.of_norm
  have hdiffNorm : Summable fun n : ℕ =>
      ‖mayerExpansionTermComplex G n (t : ℂ)
        - mayerExpansionTermComplex (Gavoid G C) n (t : ℂ)‖ := by
    exact summable_norm_iff.mpr (hsumG.sub hsumA)
  have hnorm_tsum :
      ‖(∑' n : ℕ, mayerExpansionTermComplex G n (t : ℂ))
          - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n (t : ℂ))‖
        ≤ ∑' n : ℕ,
          ‖mayerExpansionTermComplex G n (t : ℂ)
            - mayerExpansionTermComplex (Gavoid G C) n (t : ℂ)‖ := by
    rw [← hsumG.tsum_sub hsumA]
    exact norm_tsum_le_tsum_norm hdiffNorm
  have hper : ∀ n : ℕ,
      ‖mayerExpansionTermComplex G n (t : ℂ)
        - mayerExpansionTermComplex (Gavoid G C) n (t : ℂ)‖
      ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro n
    calc
      ‖mayerExpansionTermComplex G n (t : ℂ)
        - mayerExpansionTermComplex (Gavoid G C) n (t : ℂ)‖
        ≤ ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
          ‖(ursellCoefficient ω : ℂ)‖ * ∏ i, ‖(t : ℂ)‖ ^ (ω i).card :=
          norm_mayerExpansionTermComplex_sub_Gavoid_le G C n (t : ℂ)
      _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity t ω := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, clusterSeqActivity]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
      _ ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
          touchingCluster_termAbsSum_le_support_vertex_sum G C n ht
  have hper0 : (∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin 0 => allPolymers G)).filter
          (fun ω => ∃ i : Fin 0, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    obtain ⟨i, _hi⟩ := hω.2
    exact Fin.elim0 i
  have hsupportSumm : ∀ v : ι, Summable fun n : ℕ =>
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro v
    exact summable_fixedVertexTouching_termAbsSum_succ G v ht hkp hρ
  have hsupportShiftSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    classical
    induction polymerSupport C using Finset.induction_on with
    | empty => simp
    | insert v s hvs ih =>
        have hvSumm : Summable fun n : ℕ =>
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
                (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
              |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportSumm v
        simpa [Finset.sum_insert, hvs] using hvSumm.add ih
  have hsupportFullSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
    (summable_nat_add_iff 1).mp hsupportShiftSumm
  have hsupportTsum :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := by
    exact Summable.tsum_finsetSum (fun v _hv => hsupportSumm v)
  have hshiftSupport :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    rw [hsupportFullSumm.tsum_eq_zero_add, hper0, zero_add]
  have hsupport_bound :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ κ * (polymerSupport C).card := by
    calc
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity t ω := hshiftSupport
      _ = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportTsum
      _ ≤ ∑ _v ∈ polymerSupport C, κ := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hκ]
          exact fixedVertexTouching_tsum_le G v ht hkp hρ
      _ = κ * (polymerSupport C).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc
    ‖(∑' n : ℕ, mayerExpansionTermComplex G n (t : ℂ))
        - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n (t : ℂ))‖
      ≤ ∑' n : ℕ,
          ‖mayerExpansionTermComplex G n (t : ℂ)
            - mayerExpansionTermComplex (Gavoid G C) n (t : ℂ)‖ := hnorm_tsum
    _ ≤ ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
        hdiffNorm.tsum_le_tsum hper hsupportFullSumm
    _ ≤ κ * (polymerSupport C).card := hsupport_bound
    _ = ((1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by rw [hκ]

end IsingModel
