import IsingModel.RandomCurrent.Switching.GeneratingFunction
import IsingModel.RandomCurrent.Switching.SourceFilters
import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.ASourceSpinSums

/-!
# Character inversion of the subcurrent generating function (Stage C2.1b)

The `𝔽₂`-character inversion of the subcurrent binomial generating function
built in Stage C2.1a
(`Current.sum_subFinset_jointFactor_mul_prod_pow_eq_prod_one_add_pow`). Summing
the generating polynomial `P_M(σ) = ∏_e (1 + σ_u σ_v)^{M_e}` against the
`ℤ₂`-character `χ_A(σ) = ∏_{a ∈ A} (σ a).toSign` over all spin configurations
`σ : ↑Λ → Spin` extracts exactly the source-set-`A` component
`f_M(A) = ∑_{m ≤ M, ∂m = A} jointFactor(m, M − m)`, with normalization
`2^{Fintype.card ↑Λ}`.

This is the second brick (C2.1b) of the discharge of the switching gate
`hswitch'` (random-current OZ, issue #4386, thread #4418). It is pure wiring of
already-merged lemmas: the C2.1a generating function plus the
`BoundedExpansion/FiniteSums/` orthogonality spine
(`Config.sum_spinA_prod_spin_pow_eq_pow_card_iff` +
`Current.even_indicator_add_degreeAt_iff_hasSources`). The identity is a finite
character orthogonality over `Spin^{↑Λ} ≅ ℤ₂^{|Λ|}`; no analytic input, no
limit, axiom-free.

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
/-- **Character inversion (INV)**: summing the subcurrent generating polynomial
`P_M(σ) = ∏_e (1 + σ_u σ_v)^{M_e}` against the `ℤ₂`-character
`χ_A(σ) = ∏_{a ∈ A} (σ a).toSign` over all spin configurations extracts the
source-set-`A` component,
`∑_σ χ_A(σ) · P_M(σ) = 2^{|Λ|} · ∑_{m ≤ M, m.HasSources A} jointFactor(m, M − m)`.
Expand `P_M(σ)` by the C2.1a generating function
(`sum_subFinset_jointFactor_mul_prod_pow_eq_prod_one_add_pow` at the edge weight
`z_e(σ) = e.toFinset.prod (σ ·).toSign`), swap `∑_σ` with the finite subcurrent
sum, and apply the per-current orthogonality
`Config.sum_spinA_prod_spin_pow_eq_pow_card_iff` (the inner spin sum is
`2^{|Λ|}` when the parity side-condition holds, else `0`), whose side-condition
is `m.HasSources A` by `Current.even_indicator_add_degreeAt_iff_hasSources`. The
`2^{|Λ|}` counts all `Λ`-vertices (non-support vertices contribute free factors
of `2`) and cancels in the C2.1e assembly. -/
theorem Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) (A : Finset ↑Λ) :
    (∑ σ : ↑Λ → Spin,
        (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
              ^ (M e))
      = (2 : ℝ) ^ (Fintype.card ↑Λ)
        * ∑ m ∈ Current.subFinset_with_source G Λ M A,
            Current.jointFactor G Λ m (M - m) := by
  classical
  -- Step 1: expand `P_M(σ)` by the C2.1a generating function, per `σ`.
  have hexpand : ∀ σ : ↑Λ → Spin,
      (∏ e : (inducedGraph G Λ).edgeSet,
          (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
            ^ (M e))
        = ∑ m ∈ Current.subFinset G Λ M,
            Current.jointFactor G Λ m (M - m)
              * ∏ e : (inducedGraph G Λ).edgeSet,
                  ((e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
                    ^ (m e) := by
    intro σ
    exact
      (Current.sum_subFinset_jointFactor_mul_prod_pow_eq_prod_one_add_pow G Λ M
        (fun e => (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))).symm
  -- Step 2: push `χ_A` inside, swap the two finite sums.
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  -- The `simp_rw [Finset.mul_sum]` above also distributed `2^{|Λ|}` into the
  -- source-conditioned RHS sum; rewrite it as a per-current `if`-sum over
  -- `subFinset`.
  have hRHS :
      (∑ m ∈ Current.subFinset_with_source G Λ M A,
          (2 : ℝ) ^ (Fintype.card ↑Λ) * Current.jointFactor G Λ m (M - m))
        = ∑ m ∈ Current.subFinset G Λ M,
            (if m.HasSources G Λ A then
                (2 : ℝ) ^ (Fintype.card ↑Λ) * Current.jointFactor G Λ m (M - m)
              else 0) := by
    unfold Current.subFinset_with_source
    rw [Finset.sum_filter]
  rw [hRHS]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- Step 3: per-current orthogonality collapses the inner spin sum.
  have hcomm : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
        * (Current.jointFactor G Λ m (M - m)
            * ∏ e : (inducedGraph G Λ).edgeSet,
                ((e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
                  ^ (m e))
        = Current.jointFactor G Λ m (M - m)
            * ((∏ a ∈ A, ((σ a).toSign : ℝ))
                * ∏ e : (inducedGraph G Λ).edgeSet,
                    ((e : Sym2 ↑Λ).toFinset.prod
                      (fun v => ((σ v).toSign : ℝ))) ^ (m e)) :=
    fun σ => mul_left_comm _ _ _
  simp_rw [hcomm]
  rw [← Finset.mul_sum,
    Config.sum_spinA_prod_spin_pow_eq_pow_card_iff G Λ m A]
  by_cases h : m.HasSources G Λ A
  · rw [if_pos ((Current.even_indicator_add_degreeAt_iff_hasSources G Λ m A).mpr h),
      if_pos h, mul_comm]
  · rw [if_neg (fun hE =>
        h ((Current.even_indicator_add_degreeAt_iff_hasSources G Λ m A).mp hE)),
      if_neg h, mul_zero]

end Ambient
end IsingModel
