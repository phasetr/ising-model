import IsingModel.Inequalities.Lebowitz.LebowitzFour

/-!
# GJ Corollary 4.3.4: the three-point Lebowitz inequality is GHS

`cor_4_3_2_tq` at `A = {i}`, `B = {j,k}` — GJ's
`2^{3/2}⟨t_iq_jq_k⟩ ≤ 2^{3/2}⟨t_i⟩⟨q_jq_k⟩` — expands through the powerset
formulas to
`⟨σ_iσ_jσ_k⟩ − ⟨σ_iσ_j⟩⟨σ_k⟩ − ⟨σ_iσ_k⟩⟨σ_j⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩
  ≤ 2⟨σ_i⟩(⟨σ_jσ_k⟩ − ⟨σ_j⟩⟨σ_k⟩)`,
which is exactly `u₃ ≤ 0`: the GHS inequality at general `h ≥ 0`, obtained
directly with no GKS-I or truncated-two-point input.

The former `lebowitz_third` axiom asserted the strictly stronger
`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`, which is
**false**: decoupling site `i` (`J_{i·} = 0`) with `h > 0` forces
`⟨σ_jσ_k⟩ ≤ ⟨σ_j⟩⟨σ_k⟩`, contradicting strict GKS-II for a strongly coupled
edge `jk`. The axiom is deleted in this PR; its only consumer
`ghs_inequality` is rewired to `cor_4_3_4`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.3, Corollary 4.3.4, p. 61
* J. L. Lebowitz, *GHS and other inequalities*, Comm. Math. Phys. 35 (1974)
-/

namespace IsingModel

namespace Lebowitz

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
/-- Powerset of a singleton, summed: `∑_{S ⊆ {a}} f S = f ∅ + f {a}`. -/
theorem sum_powerset_singleton (a : ι) (f : Finset ι → ℝ) :
    ∑ S ∈ ({a} : Finset ι).powerset, f S = f ∅ + f {a} := by
  classical
  rw [show ({a} : Finset ι) = insert a ∅ from rfl,
    Finset.sum_powerset_insert (by simp)]
  simp only [Finset.powerset_empty, Finset.sum_singleton]

/-- **GJ Corollary 4.3.4** (the three-point Lebowitz inequality, general
`h ≥ 0`): `⟨σ_iσ_jσ_k⟩ − ⟨σ_iσ_j⟩⟨σ_k⟩ − ⟨σ_iσ_k⟩⟨σ_j⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩
≤ 2⟨σ_i⟩(⟨σ_jσ_k⟩ − ⟨σ_j⟩⟨σ_k⟩)`. Equivalently `u₃ ≤ 0`, the GHS
inequality. Proof: `cor_4_3_2_tq` with `A = {i}`, `B = {j,k}` and the
powerset formulas for the doubled `t`/`q` expectations. -/
theorem cor_4_3_4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    correlation G p {i, j, k} - correlation G p {i, j} * correlation G p {k}
      - correlation G p {i, k} * correlation G p {j}
      + correlation G p {i} * correlation G p {j, k}
    ≤ 2 * correlation G p {i} *
        (correlation G p {j, k} - correlation G p {j} * correlation G p {k}) := by
  have htq := cor_4_3_2_tq G p hf {i} {j, k}
  rw [doubleExpectation_tProd, doubleExpectation_qProd,
    doubleExpectation_tProd_mul_qProd G p {i} {j, k}
      (by simp [hij, hik])] at htq
  simp only [sum_powerset_singleton, sum_powerset_pair hjk] at htq
  -- normalise the set expressions
  simp only [Finset.sdiff_empty, Finset.sdiff_self, pair_sdiff_left hjk,
    pair_sdiff_right hjk, Finset.empty_union, Finset.union_empty,
    Finset.singleton_union, Finset.card_empty,
    Finset.card_singleton] at htq
  -- cardinality of the pair
  have hcard_jk : ({j, k} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  rw [hcard_jk] at htq
  norm_num at htq
  linarith [htq]

end Lebowitz

end IsingModel
