import IsingModel.RandomCurrent.Switching.SupportConstancy
import IsingModel.RandomCurrent.Switching.CharacterInversion

/-!
# Per-current general-source ghost-pair switch at fixed `M` (Stage C2.1d, P1-α)

The per-`M` general-source character switch: for `x ≠ y` connected in the
support graph `M.toSimpleGraph` and *any* base source set `A`, adjoining the
ghost pair `{x,y}` to `A` via symmetric difference leaves the subcurrent
binomial sum unchanged,
`f_M(A) = f_M(A △ {x,y})`, where
`f_M(A) = ∑_{m ≤ M, ∂m = A} jointFactor(m, M − m)` is the right-hand-side sum of
the character inversion C2.1b
(`Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f`).

This is the fourth brick (C2.1d) of the discharge of the switching gate
`hswitch'` (random-current OZ, issue #4386, thread #4418), generalized from base
source `∅` to arbitrary `A` (P1-α of the B2c per-edge switching identity). It
combines the pointwise identity
`(∏_{a ∈ A △ {x,y}}(σa).sign)·P_M(σ) = (∏_{a ∈ A}(σa).sign)·P_M(σ)`
(from C2.1c constancy: on the support of `P_M`, `x ↔ y` forces
`(σ x).toSign = (σ y).toSign`, whence `∏_{A △ {x,y}} = ∏_A · (σy).sign² = ∏_A`)
with character inversion C2.1b and cancellation of `2^{|Λ|} > 0`. Connectivity
is load-bearing: without `x ↔ y` the two components can differ (see the design
note's disconnected control). The base source `∅` instance
(`symmDiff ∅ {x,y} = {x,y}`) recovers the original C2.1d used by C2.1e. No
analytic input, no limit, axiom-free.

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality in Quantum Field Theory* (1992), Ch. 12.
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, Theorem 17.5.1, p. 312.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Sign-product symmetric-difference invariance**: for a real-valued `g` whose
value at `x` equals its value at `y` and whose square there is `1`, adjoining the
ghost pair `{x, y}` to a source set `A` via symmetric difference leaves the
product `∏_{a ∈ A} g a` unchanged. This is the sign algebra behind the
general-source character switch (Stage C2.1d, P1-α): the four toggle cases
collapse uniformly via `Finset.prod_union_inter` and `Finset.prod_sdiff`. Writing
`A △ {x,y} = (A ∪ {x,y}) \ (A ∩ {x,y})`, the intersection product squares to `1`
(each factor is `g x` or `g y`, each squaring to `1`) and the pair product
`g x · g y = g x · g x = 1`, so the symmetric-difference product equals `∏_A g`. -/
private lemma prod_symmDiff_pair_eq {α : Type*} [DecidableEq α]
    (g : α → ℝ) {x y : α} (hxy : x ≠ y) (hg : g x = g y)
    (hsq : g x * g x = 1) (A : Finset α) :
    ∏ a ∈ symmDiff A ({x, y} : Finset α), g a = ∏ a ∈ A, g a := by
  have hsub : A ∩ ({x, y} : Finset α) ⊆ A ∪ {x, y} :=
    Finset.inter_subset_left.trans Finset.subset_union_left
  have hsd := Finset.prod_sdiff (f := g) hsub
  have hui := Finset.prod_union_inter (f := g) (s₁ := A) (s₂ := ({x, y} : Finset α))
  have hpair : ∏ a ∈ ({x, y} : Finset α), g a = 1 := by
    rw [Finset.prod_pair hxy, ← hg, hsq]
  have hII : (∏ a ∈ A ∩ ({x, y} : Finset α), g a)
      * ∏ a ∈ A ∩ ({x, y} : Finset α), g a = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun a ha => ?_)
    rcases Finset.mem_insert.mp (Finset.mem_of_mem_inter_right ha) with rfl | ha'
    · exact hsq
    · rw [Finset.mem_singleton] at ha'
      subst ha'
      rw [← hg]; exact hsq
  rw [symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter]
  calc
    ∏ a ∈ (A ∪ {x, y}) \ (A ∩ {x, y}), g a
        = (∏ a ∈ (A ∪ {x, y}) \ (A ∩ {x, y}), g a)
            * ((∏ a ∈ A ∩ {x, y}, g a) * ∏ a ∈ A ∩ {x, y}, g a) := by
          rw [hII, mul_one]
    _ = ((∏ a ∈ (A ∪ {x, y}) \ (A ∩ {x, y}), g a) * ∏ a ∈ A ∩ {x, y}, g a)
            * ∏ a ∈ A ∩ {x, y}, g a := by ring
    _ = (∏ a ∈ A ∪ {x, y}, g a) * ∏ a ∈ A ∩ {x, y}, g a := by rw [hsd]
    _ = (∏ a ∈ A, g a) * ∏ a ∈ ({x, y} : Finset α), g a := hui
    _ = ∏ a ∈ A, g a := by rw [hpair, mul_one]

set_option linter.unusedDecidableInType false in
/-- **C2.1d (P1-α): per-`M` general-source ghost-pair switch**: for `x ≠ y`
connected in the support graph `M.toSimpleGraph` and any base source set `A`, the
source-`A` and source-`A △ {x,y}` components of the subcurrent binomial sum
coincide,
`∑_{m ≤ M, ∂m = A} jointFactor(m, M − m) = ∑_{m ≤ M, ∂m = A △ {x,y}} jointFactor(m, M − m)`.
Pointwise (VAN): for each spin config `σ`, either `P_M(σ) = 0` (both sides of
`(∏_A χ)·P_M = (∏_{A △ {x,y}} χ)·P_M` vanish), or `P_M(σ) ≠ 0`, so C2.1c
(`Current.toSign_eq_of_reachable_of_prod_ne_zero`) gives
`(σ x).toSign = (σ y).toSign`, whence `∏_{A △ {x,y}} χ = ∏_A χ` by
`prod_symmDiff_pair_eq` (`Spin.toSign_sq`). Summing VAN over `σ` and applying
character inversion C2.1b
(`Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f`) at `A` and at
`A △ {x,y}` gives `2^{|Λ|}·f_M(A) = 2^{|Λ|}·f_M(A △ {x,y})`; cancel `2^{|Λ|} > 0`
(`mul_left_cancel₀`). Generalizes the base-source `∅` C2.1d. -/
theorem Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) {x y : ↑Λ}
    (hxy : x ≠ y) (A : Finset ↑Λ)
    (hreach : (M.toSimpleGraph G Λ).Reachable x y) :
    (∑ m ∈ Current.subFinset_with_source G Λ M A,
        Current.jointFactor G Λ m (M - m))
      = ∑ m ∈ Current.subFinset_with_source G Λ M (symmDiff A {x, y}),
        Current.jointFactor G Λ m (M - m) := by
  classical
  -- Pointwise: `(∏_A χ)·P_M(σ) = (∏_{A △ {x,y}} χ)·P_M(σ)`.
  have hVAN : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
              ^ (M e)
      = (∏ a ∈ symmDiff A ({x, y} : Finset ↑Λ), ((σ a).toSign : ℝ))
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
      have hsqx : ((σ x).toSign : ℝ) * ((σ x).toSign : ℝ) = 1 := by
        have h2 : (((σ x).toSign : ℝ)) ^ 2 = 1 := by exact_mod_cast Spin.toSign_sq (σ x)
        nlinarith [h2]
      rw [prod_symmDiff_pair_eq (fun a => ((σ a).toSign : ℝ)) hxy hxy_eq hsqx A]
  -- Sum VAN, feed C2.1b at `A` and `A △ {x,y}`, cancel `2^{|Λ|}`.
  have key :
      (2 : ℝ) ^ (Fintype.card ↑Λ)
          * ∑ m ∈ Current.subFinset_with_source G Λ M A,
              Current.jointFactor G Λ m (M - m)
        = (2 : ℝ) ^ (Fintype.card ↑Λ)
          * ∑ m ∈ Current.subFinset_with_source G Λ M (symmDiff A {x, y}),
              Current.jointFactor G Λ m (M - m) := by
    rw [← Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f G Λ M A,
      ← Current.sum_spinA_mul_prod_one_add_z_pow_eq_pow_card_mul_f G Λ M
        (symmDiff A {x, y})]
    exact Finset.sum_congr rfl (fun σ _ => hVAN σ)
  exact mul_left_cancel₀ (by positivity) key

set_option linter.unusedDecidableInType false in
/-- **C2.1d (base source `∅`)**: for `x ≠ y` connected in the support graph
`M.toSimpleGraph`, the source-set-`{x,y}` and source-free components of the
subcurrent binomial sum coincide,
`∑_{m ≤ M, ∂m = {x,y}} jointFactor(m, M − m) = ∑_{m ≤ M, ∂m = ∅} jointFactor(m, M − m)`.
This is the base-source `A = ∅` instance of
`Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable`
(`symmDiff ∅ {x,y} = {x,y}`). Consumed by C2.1e
(`Current.doubledPairSummand_eq_doubledSourcefreeSummand_of_reachable`). -/
theorem Current.sum_jointFactor_pair_eq_sum_jointFactor_empty_of_reachable
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) {x y : ↑Λ}
    (hxy : x ≠ y) (hreach : (M.toSimpleGraph G Λ).Reachable x y) :
    (∑ m ∈ Current.subFinset_with_source G Λ M {x, y},
        Current.jointFactor G Λ m (M - m))
      = ∑ m ∈ Current.subFinset_with_source G Λ M ∅,
        Current.jointFactor G Λ m (M - m) := by
  have h := Current.sum_jointFactor_source_eq_symmDiff_pair_of_reachable
    G Λ M hxy ∅ hreach
  rw [show symmDiff (∅ : Finset ↑Λ) {x, y} = {x, y} by
    rw [← Finset.bot_eq_empty, bot_symmDiff]] at h
  exact h.symm

end Ambient
end IsingModel
