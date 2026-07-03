import IsingModel.RandomCurrent.Switching.PairClosedForms

/-!
# Subcurrent binomial generating function (Stage C2.1a)

The weighted binomial generating function over subcurrents, the first
algebraic brick of the discharge of the switching gate `hswitch'`
(random-current OZ, issue #4386, thread #4418). It is a direct
`z`-refinement of the merged pair closed form
`Current.sum_subFinset_jointFactor_compl_eq_pow_two`: retaining the
per-edge weights `z_e^{m_e}` instead of evaluating at `z ≡ 1`.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality in Quantum Field Theory* (1992), Ch. 12.
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, Theorem 17.5.1, p. 312.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Subcurrent binomial generating function**: for a fixed total current
`M` and real edge weights `z`,
`∑_{m ≤ M} jointFactor(m, M − m) · ∏_e z_e^{m_e} = ∏_e (1 + z_e)^{M_e}`.
Rewrite `jointFactor` per-summand as `∏_e C(M_e, m_e)`
(`jointFactor_compl_eq_prod_choose`), merge the two products, apply Fubini
for finite products/sums (`Finset.prod_univ_sum`, using
`subFinset = piFinset (range (M_e + 1))`), and close each per-edge row sum
by the binomial theorem (`add_pow`). At `z ≡ 1` it recovers
`sum_subFinset_jointFactor_compl_eq_pow_two` (`= 2^{∑_e M_e}`). -/
theorem Current.sum_subFinset_jointFactor_mul_prod_pow_eq_prod_one_add_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (M : Current G Λ) (z : (inducedGraph G Λ).edgeSet → ℝ) :
    ∑ m ∈ Current.subFinset G Λ M,
        Current.jointFactor G Λ m (M - m)
          * ∏ e : (inducedGraph G Λ).edgeSet, z e ^ (m e)
      = ∏ e : (inducedGraph G Λ).edgeSet, (1 + z e) ^ (M e) := by
  have step1 : ∀ m ∈ Current.subFinset G Λ M,
      Current.jointFactor G Λ m (M - m)
          * ∏ e : (inducedGraph G Λ).edgeSet, z e ^ (m e)
        = ∏ e : (inducedGraph G Λ).edgeSet,
            (((M e).choose (m e) : ℝ) * z e ^ (m e)) := by
    intro m hm
    rw [Current.mem_subFinset_iff] at hm
    rw [Current.jointFactor_compl_eq_prod_choose G Λ hm, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl step1]
  unfold Current.subFinset
  rw [← Finset.prod_univ_sum (fun e => Finset.range (M e + 1))
        (fun e k => ((M e).choose k : ℝ) * z e ^ k)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [add_comm (1 : ℝ) (z e), add_pow]
  exact (Finset.sum_congr rfl (fun k _ => by rw [one_pow, mul_one, mul_comm])).symm

end Ambient
end IsingModel
