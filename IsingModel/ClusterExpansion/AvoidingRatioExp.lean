import IsingModel.ClusterExpansion.AvoidingDeleteEdges
import IsingModel.ClusterExpansion.MayerCore.ComplexMayerMontroll
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient

/-!
# Avoiding-ratio exponential form

This file rewrites the vacuum high-temperature partition and the avoiding partition as
Mayer--Montroll exponentials, both on the same complex KP ball.  The avoiding partition is first
identified with the vacuum partition of the delete-edges graph `Gavoid G C`, and the KP hypotheses
are transferred from `G` to `Gavoid G C` by maximum-degree monotonicity.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The empty-boundary high-temperature sum is the complex vertex-disjoint polymer-family sum. -/
theorem htSubgraphSum_empty_eq_vdPolymerFamilies_sum_complex
    (G : SimpleGraph ι) [Fintype G.edgeSet] (z : ℂ) :
    htSubgraphSum G (∅ : Finset ι) z =
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, z ^ P.card := by
  classical
  have hAvoidEven :
      evenSubgraphsAvoiding G (∅ : Finset (Sym2 ι)) = evenSubgraphs G := by
    unfold evenSubgraphsAvoiding
    exact Finset.filter_eq_self.mpr fun Y _ => by
      simp [IsPolymerVertexDisjoint, polymerSupport_empty]
  have hAvoidHt :
      htSubgraphSum G (∅ : Finset ι) z =
        htSubgraphSumAvoiding G (∅ : Finset (Sym2 ι)) z := by
    calc
      htSubgraphSum G (∅ : Finset ι) z
          = ∑ X ∈ evenSubgraphs G, z ^ X.card :=
            htSubgraphSum_empty_eq_evenSubgraphs G z
      _ = ∑ X ∈ evenSubgraphsAvoiding G (∅ : Finset (Sym2 ι)), z ^ X.card := by
            rw [hAvoidEven]
      _ = htSubgraphSumAvoiding G (∅ : Finset (Sym2 ι)) z := by
            rfl
  have hFamilies :
      vdCompatiblePolymerFamiliesAvoiding G (∅ : Finset (Sym2 ι)) =
        vdCompatiblePolymerFamilies G := by
    unfold vdCompatiblePolymerFamiliesAvoiding
    exact Finset.filter_eq_self.mpr fun Γ _ => by
      intro P _hP
      simp [IsPolymerVertexDisjoint, polymerSupport_empty]
  calc
    htSubgraphSum G (∅ : Finset ι) z
        = htSubgraphSumAvoiding G (∅ : Finset (Sym2 ι)) z := hAvoidHt
    _ = ∑ Γ ∈ vdCompatiblePolymerFamiliesAvoiding G (∅ : Finset (Sym2 ι)),
          ∏ P ∈ Γ, z ^ P.card :=
        htSubgraphSumAvoiding_eq_vdCompatiblePolymerFamiliesAvoiding_sum G
          (∅ : Finset (Sym2 ι)) z
    _ = ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, z ^ P.card := by
        rw [hFamilies]

/-- The empty-boundary high-temperature sum is the exponential of the complex Mayer series. -/
theorem htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {R : ℝ} (hR : 0 < R)
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    htSubgraphSum G (∅ : Finset ι) z =
      Complex.exp (∑' n : ℕ, mayerExpansionTermComplex G n z) := by
  calc
    htSubgraphSum G (∅ : Finset ι) z
        = ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, z ^ P.card :=
        htSubgraphSum_empty_eq_vdPolymerFamilies_sum_complex G z
    _ = Complex.exp (∑' n : ℕ, mayerExpansionTermComplex G n z) :=
        vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex G hR hkpR hρR hz

/-- The KP conditions for `G` transfer to the delete-edges graph `Gavoid G C`. -/
theorem gavoid_kp_conditions
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {R : ℝ}
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1) :
    ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1 ∧
      4 * (((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1 := by
  classical
  by_cases hR0 : 0 ≤ R
  · have h0 :
        0 ≤ ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by
      positivity
    have h12 :
        ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
          ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) := by
      have hdeg : (Gavoid G C).maxDegree ≤ G.maxDegree :=
        maxDegree_Gavoid_le G C
      have hcast : (((Gavoid G C).maxDegree : ℝ) ≤ (G.maxDegree : ℝ)) := by
        exact_mod_cast hdeg
      gcongr
    exact kpRegion_downward_closed h0 h12 hkpR hρR
  · have hRlt : R < 0 := lt_of_not_ge hR0
    set r : ℝ := ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)
    have hfactor_nonpos : Real.exp 1 * R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos 1)) (le_of_lt hRlt)
    have hr_nonpos : r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hfactor_nonpos
    have hr_lt_one : r < 1 :=
      lt_of_le_of_lt hr_nonpos zero_lt_one
    have hnum_nonpos : 4 * r ≤ 0 := by
      nlinarith
    have hden_nonneg : 0 ≤ (1 - r) ^ 2 :=
      sq_nonneg _
    have hratio_nonpos : 4 * r / (1 - r) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    exact
      ⟨by simpa [r] using hr_lt_one,
       by simpa [r] using lt_of_le_of_lt hratio_nonpos zero_lt_one⟩

/-- The avoiding-to-vacuum ratio is bounded by the exponential of the Mayer-sum difference. -/
theorem norm_htSubgraphSumAvoiding_div_htSubgraphSum_empty_le
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {R : ℝ} (hR : 0 < R)
    (hkpR : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρR : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖htSubgraphSumAvoiding G C z / htSubgraphSum G (∅ : Finset ι) z‖
      ≤ Real.exp ‖(∑' n : ℕ, mayerExpansionTermComplex G n z)
          - (∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n z)‖ := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  obtain ⟨hkpAvoid, hρAvoid⟩ := gavoid_kp_conditions (G := G) (C := C) hkpR hρR
  let MG : ℂ := ∑' n : ℕ, mayerExpansionTermComplex G n z
  let MA : ℂ := ∑' n : ℕ, mayerExpansionTermComplex (Gavoid G C) n z
  have hFull :
      htSubgraphSum G (∅ : Finset ι) z = Complex.exp MG := by
    simpa [MG] using
      htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex (G := G)
        hR hkpR hρR hz
  have hAvoid :
      htSubgraphSumAvoiding G C z = Complex.exp MA := by
    calc
      htSubgraphSumAvoiding G C z
          = htSubgraphSum (Gavoid G C) (∅ : Finset ι) z :=
          htSubgraphSumAvoiding_eq_htSubgraphSum_empty_Gavoid G C z
      _ = Complex.exp MA := by
          simpa [MA] using
            htSubgraphSum_empty_eq_exp_tsum_mayerExpansionTermComplex
              (G := Gavoid G C) hR hkpAvoid hρAvoid hz
  calc
    ‖htSubgraphSumAvoiding G C z / htSubgraphSum G (∅ : Finset ι) z‖
        = ‖Complex.exp MA / Complex.exp MG‖ := by
          rw [hAvoid, hFull]
    _ = ‖Complex.exp (MA - MG)‖ := by
          rw [← Complex.exp_sub]
    _ = Real.exp (MA - MG).re := by
          rw [Complex.norm_exp]
    _ ≤ Real.exp ‖MG - MA‖ := by
          apply Real.exp_le_exp.mpr
          calc
            (MA - MG).re ≤ ‖MA - MG‖ := Complex.re_le_norm _
            _ = ‖MG - MA‖ := norm_sub_rev MA MG

end IsingModel
