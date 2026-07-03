import IsingModel.RandomCurrent.Switching.SupportConstancy
import IsingModel.RandomCurrent.Switching.CharacterInversion

/-!
# Per-current source-set vanishing at fixed `M` (Stage C2.1d)

The per-`M` source-set equality: for `x ≠ y` connected in the support graph
`M.toSimpleGraph`, the source-set-`{x,y}` component equals the source-free
component,
`f_M({x,y}) = f_M(∅)`, where
`f_M(A) = ∑_{m ≤ M, ∂m = A} jointFactor(m, M − m)` is the right-hand-side sum of
the character inversion C2.1b
(`Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f`).

This is the fourth brick (C2.1d) of the discharge of the switching gate
`hswitch'` (random-current OZ, issue #4386, thread #4418). It combines the
pointwise vanishing identity `χ_{x,y}(σ) · P_M(σ) = χ_∅(σ) · P_M(σ)`
(from C2.1c constancy: on the support of `P_M`, `x ↔ y` forces
`(σ x).toSign = (σ y).toSign`, whence `χ_{x,y} = (σ y).toSign² = 1 = χ_∅`) with
character inversion C2.1b and cancellation of `2^{|Λ|} > 0`. Connectivity is
load-bearing: without `x ↔ y` the two components can differ (see the design
note's disconnected control). No analytic input, no limit, axiom-free.

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
/-- **C2.1d: per-`M` source-set equality**: for `x ≠ y` connected in the support
graph `M.toSimpleGraph`, the source-set-`{x,y}` and source-free components of the
subcurrent binomial sum coincide,
`∑_{m ≤ M, ∂m = {x,y}} jointFactor(m, M − m) = ∑_{m ≤ M, ∂m = ∅} jointFactor(m, M − m)`.
Pointwise vanishing (VAN): for each spin config `σ`, either `P_M(σ) = 0` (both
sides of `χ_{x,y}(σ)·P_M(σ) = χ_∅(σ)·P_M(σ)` vanish), or `P_M(σ) ≠ 0`, so C2.1c
(`Current.toSign_eq_of_reachable_of_prod_ne_zero`) gives
`(σ x).toSign = (σ y).toSign`, whence `χ_{x,y}(σ) = (σ y).toSign² = 1 = χ_∅(σ)`
(`Spin.toSign_sq`). Summing VAN over `σ` and applying character inversion C2.1b
(`Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f`) at `A = {x,y}` and
`A = ∅` gives `2^{|Λ|}·f_M({x,y}) = 2^{|Λ|}·f_M(∅)`; cancel `2^{|Λ|} > 0`
(`mul_left_cancel₀`). -/
theorem Current.sum_jointFactor_pair_eq_sum_jointFactor_empty_of_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) {x y : ↑Λ}
    (hxy : x ≠ y) (hreach : (M.toSimpleGraph G Λ).Reachable x y) :
    (∑ m ∈ Current.subFinset_with_source G Λ M {x, y},
        Current.jointFactor G Λ m (M - m))
      = ∑ m ∈ Current.subFinset_with_source G Λ M ∅,
        Current.jointFactor G Λ m (M - m) := by
  classical
  -- Pointwise vanishing: `χ_{x,y}(σ)·P_M(σ) = χ_∅(σ)·P_M(σ)`.
  have hVAN : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ ({x, y} : Finset ↑Λ), ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
              ^ (M e)
      = (∏ a ∈ (∅ : Finset ↑Λ), ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
              ^ (M e) := by
    intro σ
    rcases eq_or_ne
        (∏ e : (inducedGraph G Λ).edgeSet,
          (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
            ^ (M e)) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · have hxy_eq :=
        Current.toSign_eq_of_reachable_of_prod_ne_zero G Λ M σ h0 hreach
      have hsq : ((σ y).toSign : ℝ) * ((σ y).toSign : ℝ) = 1 := by
        have h2 : (((σ y).toSign : ℝ)) ^ 2 = 1 := by exact_mod_cast Spin.toSign_sq (σ y)
        nlinarith [h2]
      rw [Finset.prod_pair hxy, Finset.prod_empty, hxy_eq, hsq, one_mul]
  -- Sum VAN, feed C2.1b at `A = {x,y}` and `A = ∅`, cancel `2^{|Λ|}`.
  have key :
      (2 : ℝ) ^ (Fintype.card ↑Λ)
          * ∑ m ∈ Current.subFinset_with_source G Λ M {x, y},
              Current.jointFactor G Λ m (M - m)
        = (2 : ℝ) ^ (Fintype.card ↑Λ)
          * ∑ m ∈ Current.subFinset_with_source G Λ M ∅,
              Current.jointFactor G Λ m (M - m) := by
    rw [← Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f G Λ M {x, y},
      ← Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f G Λ M ∅]
    exact Finset.sum_congr rfl (fun σ _ => hVAN σ)
  exact mul_left_cancel₀ (by positivity) key

end Ambient
end IsingModel
