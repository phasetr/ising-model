import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.EvenSubgraphs
import IsingModel.ClusterExpansion.Families.VertexDisjoint
import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.ClusterExpansion.MayerCore.UrsellMajorant
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.EdgeInclusionExclusion
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre.FamilyTupleSum

/-!
# The `r!`-to-one colour-class fibre (4/5): colour-degree bounds

Structural split (4/5) of
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre`.
This child holds the Mayer term and the log-Taylor term in colouring form together with the
analytic majorants: the colouring count bound `#colourings ≤ k^r`, the per-`(r,k)` bound, the
row bound, and the summability of `∑ (r^r/r!)|A|^r`.  See the
`IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ColorClassFibre` facade module for the
full contents overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mayer term as a colour-degree double sum**: distributing the colour-degree sum out of the
sequence sum, the `r`-th Mayer term is
`∑_{k=1}^r (-1)^(k-1)/k · ∑_ω #properSurjectiveColorings(G(ω),k)/r! · clusterSeqActivity`.
The inner sum is the per-`(r,k)` colouring contribution feeding the capstone Fubini swap. -/
theorem mayerExpansionTerm_eq_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (r : ℕ) (t : ℝ) :
    mayerExpansionTerm G r t =
      ∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω := by
  rw [mayerExpansionTerm_eq_coloring_form]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- **Log-Taylor term as a colouring sum**: combining the log-Taylor expansion
(`logTaylor_eps_term_eq_sum_vdFamilyTuples`, family-tuple form) with the per-`m` identity
(`vdFamilyTuple_sum_eq_seq_coloring_sum`, `m = n+1`), the `n`-th log-Taylor term equals the
`m=n+1` colouring contribution summed over sequence lengths `r ≤ (n+1)·|allPolymers G|`. -/
theorem logTaylor_term_eq_coloring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdCompatiblePolymerFamilies G).erase ∅, ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
        (n + 1) =
      ∑ r ∈ Finset.range ((n + 1) * (allPolymers G).card + 1),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) (n + 1)).card : ℝ) /
              (r.factorial : ℝ) * clusterSeqActivity t ω := by
  rw [logTaylor_eps_term_eq_sum_vdFamilyTuples, ← Finset.mul_sum,
    vdFamilyTuple_sum_eq_seq_coloring_sum, Finset.mul_sum]

/-- **Proper surjective colourings are bounded by all colourings**: at most `k^r` proper
surjective `k`-colourings of a graph on `Fin r` (they are a subset of all functions
`Fin r → Fin k`).  Used for the double-summability majorant in the capstone. -/
theorem card_properSurjectiveColorings_le {r : ℕ} (H : SimpleGraph (Fin r)) [DecidableRel H.Adj]
    (k : ℕ) : (properSurjectiveColorings H k).card ≤ k ^ r := by
  classical
  calc (properSurjectiveColorings H k).card
      ≤ (Finset.univ : Finset (Fin r → Fin k)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = k ^ r := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Per-`(r,k)` colour-degree term bound**: the absolute value of the `(r,k)` colour-degree
contribution is bounded by `(k^(r-1)/r!)·A^r`, where `A = ∑_{P∈allPolymers G} |t|^|P|`.  Combines
`card_properSurjectiveColorings_le` (`#colourings ≤ k^r`) and `sum_clusterSeqActivity_abs_piFinset`
(`∑_ω |activity| = A^r`).  The brick of the capstone double-summability majorant. -/
theorem abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r k : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hkpos, one_div]
  have hsum : |∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
          (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
    calc |∑ ω ∈ _, _| ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            |((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
              (r.factorial : ℝ) * clusterSeqActivity t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
            ((k : ℝ) ^ r / (r.factorial : ℝ)) * |clusterSeqActivity t ω| := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          rw [abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]
          gcongr
          exact_mod_cast card_properSurjectiveColorings_le (polymerSeqIncompatibilityGraph ω) k
      _ = ((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
          rw [← Finset.mul_sum, sum_clusterSeqActivity_abs_piFinset]
  have hkr : (k : ℝ)⁻¹ * (k : ℝ) ^ r = (k : ℝ) ^ (r - 1) := by
    have h1 : (k : ℝ) ^ r = (k : ℝ) * (k : ℝ) ^ (r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkpos), one_mul]
  calc (k : ℝ)⁻¹ * |∑ ω ∈ _, _|
      ≤ (k : ℝ)⁻¹ *
          (((k : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r) := by
        gcongr
    _ = ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        rw [← mul_assoc, ← mul_div_assoc, hkr]

/-- **Colour-degree row bound**: `∑_{k=1}^r |C(r,k)| ≤ (r^r/r!)·A^r`, the per-row majorant
of the capstone double sum, summing `abs_colorDegreeTerm_le` over `k ∈ Icc 1 r` (each
`k^(r-1) ≤ r^(r-1)`, and `Icc 1 r` has `r` elements so `r·r^(r-1) = r^r`). -/
theorem sum_abs_colorDegreeTerm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [Fintype G.edgeSet] (t : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Icc 1 r, |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * clusterSeqActivity t ω| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
  calc ∑ k ∈ Finset.Icc 1 r, |((-1 : ℝ) ^ (k - 1) / (k : ℝ)) * _|
      ≤ ∑ k ∈ Finset.Icc 1 r,
          ((r : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        refine (abs_colorDegreeTerm_le G t r k hk.1 hr).trans ?_
        gcongr
        exact_mod_cast hk.2
    _ = ((r : ℝ) ^ r / (r.factorial : ℝ)) * (∑ P ∈ allPolymers G, |t| ^ P.card) ^ r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        have hrr : (r : ℝ) * (r : ℝ) ^ (r - 1) = (r : ℝ) ^ r := by
          rw [← pow_succ', Nat.sub_add_cancel hr]
        rw [← mul_assoc, ← mul_div_assoc, hrr]

/-- **Summable self-power factorial majorant**: `∑_r (r^r/r!)·|A|^r` converges for `e·|A| < 1`
(ratio test: the ratio `(1+1/(r+1))^(r+1)·|A| → e·|A| < 1`, bounded via `Real.add_one_le_exp`).
The row-majorant series for the capstone double-summability. -/
theorem summable_pow_self_div_factorial_mul_abs_pow (A : ℝ) (hA : Real.exp 1 * |A| < 1) :
    Summable fun r : ℕ => ((r : ℝ) ^ r / (r.factorial : ℝ)) * |A| ^ r := by
  refine summable_of_ratio_norm_eventually_le hA ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hnnA : (0 : ℝ) ≤ ((↑(m + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) * |A| ^ (m + 1) := by
    positivity
  have hnnB : (0 : ℝ) ≤
      ((↑(m + 1 + 1) : ℝ) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ)) * |A| ^ (m + 1 + 1) := by
    positivity
  rw [Real.norm_of_nonneg hnnB, Real.norm_of_nonneg hnnA]
  have hratio : (↑(m + 1 + 1) : ℝ) / (↑(m + 1) : ℝ) = 1 + 1 / (↑(m + 1) : ℝ) := by
    push_cast; field_simp
  have hle : (1 + 1 / (↑(m + 1) : ℝ)) ^ (m + 1) ≤ Real.exp 1 := by
    calc (1 + 1 / (↑(m + 1) : ℝ)) ^ (m + 1)
        ≤ (Real.exp (1 / (↑(m + 1) : ℝ))) ^ (m + 1) := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hkey : (↑(m + 1 + 1) : ℝ) ^ (m + 1) ≤ Real.exp 1 * (↑(m + 1) : ℝ) ^ (m + 1) := by
    have h := mul_le_mul_of_nonneg_right hle
      (by positivity : (0 : ℝ) ≤ (↑(m + 1) : ℝ) ^ (m + 1))
    rwa [← mul_pow,
      show (1 + 1 / (↑(m + 1) : ℝ)) * (↑(m + 1) : ℝ) = (↑(m + 1 + 1) : ℝ) from by
        push_cast; field_simp] at h
  have e_fac : ((m + 1 + 1).factorial : ℝ) = (↑(m + 1 + 1) : ℝ) * ((m + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ (m + 1), Nat.cast_mul]
  have e_pow : (↑(m + 1 + 1) : ℝ) ^ (m + 1 + 1) =
      (↑(m + 1 + 1) : ℝ) * (↑(m + 1 + 1) : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have e_R : |A| ^ (m + 1 + 1) = |A| ^ (m + 1) * |A| := by rw [pow_succ]
  rw [e_fac, e_pow, e_R, mul_div_mul_left _ _ (by positivity : (↑(m + 1 + 1) : ℝ) ≠ 0)]
  calc (↑(m + 1 + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * (|A| ^ (m + 1) * |A|)
      = (↑(m + 1 + 1) : ℝ) ^ (m + 1) *
          (|A| ^ (m + 1) * |A| / ((m + 1).factorial : ℝ)) := by ring
    _ ≤ (Real.exp 1 * (↑(m + 1) : ℝ) ^ (m + 1)) *
          (|A| ^ (m + 1) * |A| / ((m + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = Real.exp 1 * |A| *
          ((↑(m + 1) : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * |A| ^ (m + 1)) := by ring

end IsingModel
