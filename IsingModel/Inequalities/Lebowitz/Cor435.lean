import IsingModel.Inequalities.Lebowitz.Cor434
import IsingModel.Inequalities.GKS

/-!
# GJ Corollary 4.3.5, the inductive Lebowitz bound

The intermediate inequality of GJ's proof of Corollary 4.3.5 (p. 62):
for `j, k ∉ S`, `j ≠ k`, ferromagnetic `h ≥ 0`,

`⟨σ_{S∪{j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + ∑_{T ⊆ S} ⟨σ_{T∪{j}}⟩⟨σ_{(S\T)∪{k}}⟩`.

Derivation (GJ p. 62, "Dropping negative terms from the right (B₂ odd) and
all terms with B₂ even and the A partition nontrivial"): apply
`cor_4_3_2_tq` with `A = S`, `B = {j,k}`; drop the odd part of the
right-hand side (GKS-I), cancel the non-trivial even terms pairwise via
GKS-II (`⟨σ_X⟩⟨σ_jσ_k⟩ ≤ ⟨σ_{X∪{j,k}}⟩` for `X ⊆ S`), and move the `q`-odd
terms to the right after the reflection `X ↦ S \ X`.

This replaces the former `lebowitz_inductive` axiom in
`Inequalities/GHS/NPoint.lean` (which, unlike `lebowitz_four` and
`lebowitz_third`, was true as stated).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Corollary 4.3.5, p. 62
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- Reflection of a powerset sum along `X ↦ S \ X`. -/
theorem sum_powerset_reflect (S : Finset ι) (f : Finset ι → Finset ι → ℝ) :
    ∑ X ∈ S.powerset, f X (S \ X) = ∑ X ∈ S.powerset, f (S \ X) X := by
  refine Finset.sum_nbij' (fun X => S \ X) (fun X => S \ X)
    (fun X hX => Finset.mem_powerset.2 (Finset.sdiff_subset))
    (fun X hX => Finset.mem_powerset.2 (Finset.sdiff_subset))
    (fun X hX => Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hX))
    (fun X hX => Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hX))
    (fun X hX => ?_)
  rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hX)]

omit [Fintype ι] in
/-- `X ∪ {a} = insert a X` for `Finset`. -/
theorem union_singleton_eq_insert (X : Finset ι) (a : ι) :
    X ∪ {a} = insert a X := by
  rw [Finset.union_comm, Finset.singleton_union]

/-- **The inductive Lebowitz bound** (GJ §4.3, the intermediate inequality
in the proof of Corollary 4.3.5, p. 62): for ferromagnetic `h ≥ 0`, a set
`S` and two sites `j, k ∉ S` with `j ≠ k`,
`⟨σ_{S∪{j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + ∑_{T ⊆ S} ⟨σ_{T∪{j}}⟩⟨σ_{(S\T)∪{k}}⟩`.
Proof: `cor_4_3_2_tq` at `A = S`, `B = {j,k}`; the right-hand odd part is
dropped by GKS-I, the non-trivial even terms cancel pairwise by GKS-II,
and the `q`-odd terms move right after the reflection `X ↦ S \ X`. -/
theorem lebowitz_inductive_bound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (S : Finset ι) (j k : ι) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlation G p (insert j (insert k S)) ≤
    correlation G p S * correlation G p {j, k} +
    ∑ T ∈ S.powerset,
      correlation G p (insert j T) * correlation G p (insert k (S \ T)) := by
  have htq := cor_4_3_2_tq G p hf S {j, k}
  rw [doubleExpectation_tProd, doubleExpectation_qProd,
    doubleExpectation_tProd_mul_qProd G p S {j, k}
      (by
        rw [Finset.disjoint_right]
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact fun h => hj h
        · rw [Finset.mem_singleton] at ha
          subst ha
          exact fun h => hk h)] at htq
  simp only [sum_powerset_pair hjk] at htq
  simp only [Finset.sdiff_empty, Finset.sdiff_self, pair_sdiff_left hjk,
    pair_sdiff_right hjk, Finset.union_empty, Finset.card_empty,
    Finset.card_singleton, correlation_empty] at htq
  have hcard_jk : ({j, k} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  rw [hcard_jk] at htq
  norm_num at htq
  -- abbreviations for the five powerset sums
  set c : Finset ι → ℝ := correlation G p with hc
  -- nonnegativity of all correlations
  have hcnn : ∀ X : Finset ι, 0 ≤ c X := fun X => gks_first G p hf X
  -- the four powerset sums
  set P := ∑ X ∈ S.powerset, c X * c (insert j (insert k (S \ X))) with hP
  set R := ∑ X ∈ S.powerset, c (insert j X) * c (insert k (S \ X)) with hR
  set R' := ∑ X ∈ S.powerset, c (insert k X) * c (insert j (S \ X)) with hR'
  set Q := ∑ X ∈ S.powerset, c (insert j (insert k X)) * c (S \ X) with hQ
  set A := ∑ X ∈ S.powerset, c X * c (S \ X) with hA
  have hexp : ∑ X ∈ S.powerset,
      (c X * c (insert j (insert k (S \ X)))
        + -(c (insert j X) * c (insert k (S \ X)))
        + -(c (insert k X) * c (insert j (S \ X)))
        + c (insert j (insert k X)) * c (S \ X))
      = P + -R + -R' + Q := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, hP, hR, hR', hQ]
  rw [hexp] at htq
  -- reflection: the `T = ∅` mixed sum equals the `T = {j,k}` mixed sum
  have hPQ : P = Q := by
    rw [hP, sum_powerset_reflect S (fun X Y => c X * c (insert j (insert k Y))), hQ]
    exact Finset.sum_congr rfl fun X _ => mul_comm _ _
  -- reflection: the two `q`-odd mixed sums agree
  have hRR : R' = R := by
    rw [hR', sum_powerset_reflect S (fun X Y => c (insert k X) * c (insert j Y)), hR]
    exact Finset.sum_congr rfl fun X _ => mul_comm _ _
  -- A and its parts are non-negative
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun X _ => mul_nonneg (hcnn _) (hcnn _)
  have hjknn : 0 ≤ c {j} * c {k} := mul_nonneg (hcnn _) (hcnn _)
  -- per-term GKS-II domination on the powerset
  have hgks2 : ∀ X ∈ S.powerset,
      c X * c (S \ X) * c {j, k} ≤ c (insert j (insert k X)) * c (S \ X) := by
    intro X hX
    have hXS := Finset.mem_powerset.1 hX
    have hdisj : Disjoint X ({j, k} : Finset ι) := by
      rw [Finset.disjoint_right]
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact fun h => hj (hXS h)
      · rw [Finset.mem_singleton] at ha
        subst ha
        exact fun h => hk (hXS h)
    have h2 := gks_second G p hf X {j, k}
    rw [hdisj.symmDiff_eq_sup] at h2
    have h3 : X ⊔ ({j, k} : Finset ι) = insert j (insert k X) := by
      change X ∪ ({j, k} : Finset ι) = insert j (insert k X)
      rw [show ({j, k} : Finset ι) = insert j {k} from rfl,
        Finset.union_insert, union_singleton_eq_insert]
    rw [h3] at h2
    calc c X * c (S \ X) * c {j, k}
        = c X * c {j, k} * c (S \ X) := by ring
      _ ≤ c (insert j (insert k X)) * c (S \ X) :=
          mul_le_mul_of_nonneg_right h2 (hcnn _)
  -- split off the `X = S` terms
  have hcempty : c ∅ = 1 := by rw [hc]; exact correlation_empty G p
  have hQsplit : c (insert j (insert k S))
      + ∑ X ∈ S.powerset.erase S, c (insert j (insert k X)) * c (S \ X) = Q := by
    have h := Finset.add_sum_erase S.powerset
      (fun X => c (insert j (insert k X)) * c (S \ X)) (Finset.mem_powerset_self S)
    simp only [Finset.sdiff_self, hcempty, mul_one] at h
    exact h
  have hAsplit : c S + ∑ X ∈ S.powerset.erase S, c X * c (S \ X) = A := by
    have h := Finset.add_sum_erase S.powerset
      (fun X => c X * c (S \ X)) (Finset.mem_powerset_self S)
    simp only [Finset.sdiff_self, hcempty, mul_one] at h
    exact h
  -- multiply the A-split by `c {j,k}` and dominate the rest termwise
  have hAa : A * c {j, k} = c S * c {j, k}
      + ∑ X ∈ S.powerset.erase S, c X * c (S \ X) * c {j, k} := by
    rw [← hAsplit, add_mul, Finset.sum_mul]
  have hdom : ∑ X ∈ S.powerset.erase S, c X * c (S \ X) * c {j, k}
      ≤ ∑ X ∈ S.powerset.erase S, c (insert j (insert k X)) * c (S \ X) :=
    Finset.sum_le_sum fun X hX => hgks2 X (Finset.mem_of_mem_erase hX)
  -- assemble
  have hrhs : A * (c {j, k} + -(c {j} * c {k}) + -(c {k} * c {j}) + c {j, k})
      = 2 * (A * c {j, k}) - 2 * (A * (c {j} * c {k})) := by ring
  rw [hrhs] at htq
  have hAcc : 0 ≤ A * (c {j} * c {k}) := mul_nonneg hAnn hjknn
  linarith

end Lebowitz

end IsingModel
