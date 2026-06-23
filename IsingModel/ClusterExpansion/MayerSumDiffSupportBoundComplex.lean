import IsingModel.ClusterExpansion.MayerSumDiffSupportBound

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Complex local KP bound for the Mayer-sum difference caused by avoiding a support.**  On
KP parameters measured at the complex activity norm `‖z‖`, the norm of the difference between
the full Mayer sum and the Mayer sum of `Gavoid G C` is bounded by the fixed-vertex KP constant
times `|polymerSupport C|`.  This is the complex-activity version of
`norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card`; the proof is the same
support-union and fixed-vertex touching argument, with the real activity specialized to
`t := ‖z‖`. -/
theorem norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card_complex
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {z : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2 < 1) :
    ‖(∑' n : ℕ, mayerExpansionTermComplex G n z)
        - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n z)‖
      ≤ ((1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hkpAbs : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|) < 1 := by
    simpa [abs_of_nonneg hz_nonneg] using hkp
  have hρAbs : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|))
      / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |‖z‖|)) ^ 2 < 1 := by
    simpa [abs_of_nonneg hz_nonneg] using hρ
  set κ : ℝ := (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2)⁻¹ ^ 2 with hκ
  obtain ⟨hkpAvoid, hρAvoid⟩ := gavoid_kp_conditions (G := G) (C := C) (R := ‖z‖) hkp hρ
  have hsuccG : Summable fun n : ℕ => ‖mayerExpansionTermComplex G (n + 1) z‖ := by
    exact summable_norm_mayerExpansionTermComplex_succ_of_tail_condition (G := G) hkp hρ
  have hsuccA : Summable fun n : ℕ =>
      ‖mayerExpansionTermComplex (Gavoid G C) (n + 1) z‖ := by
    exact summable_norm_mayerExpansionTermComplex_succ_of_tail_condition
      (G := Gavoid G C) hkpAvoid hρAvoid
  have hsumG : Summable fun n : ℕ => mayerExpansionTermComplex G n z :=
    (summable_nat_add_iff 1).mp hsuccG.of_norm
  have hsumA : Summable fun n : ℕ => mayerExpansionTermComplex (Gavoid G C) n z :=
    (summable_nat_add_iff 1).mp hsuccA.of_norm
  have hdiffNorm : Summable fun n : ℕ =>
      ‖mayerExpansionTermComplex G n z
        - mayerExpansionTermComplex (Gavoid G C) n z‖ := by
    exact summable_norm_iff.mpr (hsumG.sub hsumA)
  have hnorm_tsum :
      ‖(∑' n : ℕ, mayerExpansionTermComplex G n z)
          - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n z)‖
        ≤ ∑' n : ℕ,
          ‖mayerExpansionTermComplex G n z
            - mayerExpansionTermComplex (Gavoid G C) n z‖ := by
    rw [← hsumG.tsum_sub hsumA]
    exact norm_tsum_le_tsum_norm hdiffNorm
  have hper : ∀ n : ℕ,
      ‖mayerExpansionTermComplex G n z
        - mayerExpansionTermComplex (Gavoid G C) n z‖
      ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
    intro n
    calc
      ‖mayerExpansionTermComplex G n z
        - mayerExpansionTermComplex (Gavoid G C) n z‖
        ≤ ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
          ‖(ursellCoefficient ω : ℂ)‖ * ∏ i, ‖z‖ ^ (ω i).card :=
          norm_mayerExpansionTermComplex_sub_Gavoid_le G C n z
      _ = ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, clusterSeqActivity]
      _ ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω :=
          touchingCluster_termAbsSum_le_support_vertex_sum G C n hz_nonneg
  have hper0 : (∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin 0 => allPolymers G)).filter
          (fun ω => ∃ i : Fin 0, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    obtain ⟨i, _hi⟩ := hω.2
    exact Fin.elim0 i
  have hsupportSumm : ∀ v : ι, Summable fun n : ℕ =>
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
    intro v
    exact summable_fixedVertexTouching_termAbsSum_succ G v hz_nonneg hkpAbs hρAbs
  have hsupportShiftSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
    classical
    induction polymerSupport C using Finset.induction_on with
    | empty => simp
    | insert v s hvs ih =>
        have hvSumm : Summable fun n : ℕ =>
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
                (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
              |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := hsupportSumm v
        simpa [Finset.sum_insert, hvs] using hvSumm.add ih
  have hsupportFullSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω :=
    (summable_nat_add_iff 1).mp hsupportShiftSumm
  have hsupportTsum :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω)
      = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
    exact Summable.tsum_finsetSum (fun v _hv => hsupportSumm v)
  have hshiftSupport :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω)
      = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := by
    rw [hsupportFullSumm.tsum_eq_zero_add, hper0, zero_add]
  have hsupport_bound :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω)
      ≤ κ * (polymerSupport C).card := by
    calc
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω)
        = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
            (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := hshiftSupport
      _ = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω := hsupportTsum
      _ ≤ ∑ _v ∈ polymerSupport C, κ := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hκ]
          simpa [abs_of_nonneg hz_nonneg] using
            (fixedVertexTouching_tsum_le (G := G) (v := v) (t := ‖z‖)
              hz_nonneg hkpAbs hρAbs)
      _ = κ * (polymerSupport C).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc
    ‖(∑' n : ℕ, mayerExpansionTermComplex G n z)
        - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n z)‖
      ≤ ∑' n : ℕ,
          ‖mayerExpansionTermComplex G n z
            - mayerExpansionTermComplex (Gavoid G C) n z‖ := hnorm_tsum
    _ ≤ ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity ‖z‖ ω :=
        hdiffNorm.tsum_le_tsum hper hsupportFullSumm
    _ ≤ κ * (polymerSupport C).card := hsupport_bound
    _ = ((1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)))
          * (1 - 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ‖z‖)) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by rw [hκ]

end IsingModel
