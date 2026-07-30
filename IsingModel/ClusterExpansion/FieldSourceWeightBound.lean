import IsingModel.ClusterExpansion.FieldSourceAvoidFactor
import IsingModel.ClusterExpansion.FieldPolymerExpNonvanishing

/-!
# Per-source complex weight geometric bound (GJ §17.6.1, brick F5a-1)

Brick F5a-1 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  This is the **first genuinely new
analytic sub-brick** of the field cluster expansion: it turns the per-source
summand of the two-point numerator into a geometric term `A₀·a₀^{|S|}` whose
ratio `a₀` is independent of the volume.

The source-peel identity `fieldTwoPointNumℂ_eq_sum_source_avoid`
(`FieldSourcePeel.lean`) writes the numerator as
`∑_{S ∈ fieldSourceConfigs G A} w^ℂ_A(S) · Zᶠ(GavoidVertex G (polymerSupport S ∪ A)) / Zᶠ(G)`,
where `w^ℂ_A(S) = fieldSourceWeightℂ A a b S` and the avoiding collar is
`polymerSupport S ∪ A` (matching the vertex set fed to the F5-pre-2a
ratio bound `fieldPolymerZℂ_GavoidVertex_div_norm_le_exp`).  This file bounds the
**weight** factor together with the collar `exp`-factor that the ratio bound
contributes, in a form parametric in the aggregation exponent `κ` so that the
geometric aggregation (F5a-3) can instantiate `κ := κ_Δ` cleanly and stay
decoupled from the fiber-counting (F5a-2).

## Main statements
* `polymerSupport_card_le_two_mul_card` — universal parity bound
  `|polymerSupport P| ≤ 2·|P|` (no membership hypothesis), the collar analogue of
  `oddBoundary_card_le_two_mul_card`.
* `fieldSourceWeightℂ_norm_le` (private) — inequality (I):
  `‖w^ℂ_A(S)‖ ≤ Mr^{|A|}·(Mr²·|tanh a|)^{|S|}`, with `Mr := max(1, ‖tanh_ℂ b‖)`
  (threaded as `hMr1 : 1 ≤ Mr`, `hMr : ‖tanh_ℂ b‖ ≤ Mr`).
* `fieldSourceWeightℂ_norm_mul_exp_le` — capstone, parametric-`κ` form:
  `‖w^ℂ_A(S)‖ · exp(κ·|polymerSupport S ∪ A|)
     ≤ Mr^{|A|}·exp(κ·|A|) · (Mr²·e^{2κ}·|tanh a|)^{|S|}`.

The two `|S|`-powers on the right are the geometric ratio base `a₀` of F5a-3;
the fiber count `|{S : |S|=ℓ}| ≤ (c_A·Δ²)^ℓ` and the geometric sum are deferred
to bricks F5a-2 / F5a-3.

## References
- Friedli–Velenik §3.7.3, eqs. (3.41)–(3.48), pp. 116–117, is the `h = 0`
  template. Exercise 5.8, p. 238, with its Appendix C solution, p. 531, gives
  the exact field weight. The per-source complex bound is a project extension.
- Glimm–Jaffe §18.3, eq. (18.3.3), p. 330, is a continuum P(φ)₂ analogy only;
  not a lattice-Ising source. It is not a polymer-activity source either.
-/

namespace IsingModel

open Finset
open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Universal support parity bound `|supp P| ≤ 2·|P|`**: the support of a
polymer `P` (a set of `|P|` edges) has at most `2·|P|` vertices.  Every support
vertex lies on some edge of `P`, so `polymerSupport P ⊆ ⋃_{e ∈ P} e`, and each
edge contributes at most `2` vertices (`Sym2.card_toFinset ≤ 2`).  The collar
analogue of `oddBoundary_card_le_two_mul_card`, with no membership hypothesis;
supplies `|polymerSupport S ∪ A| ≤ 2|S| + |A|` for the F5a-1 collar `exp`-factor. -/
theorem polymerSupport_card_le_two_mul_card (P : Finset (Sym2 ι)) :
    (polymerSupport P).card ≤ 2 * P.card := by
  classical
  have hsub : polymerSupport P ⊆ P.biUnion Sym2.toFinset := by
    intro v hv
    rw [mem_polymerSupport] at hv
    obtain ⟨e, heP, hve⟩ := hv
    exact Finset.mem_biUnion.mpr ⟨e, heP, Sym2.mem_toFinset.mpr hve⟩
  calc (polymerSupport P).card
      ≤ (P.biUnion Sym2.toFinset).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ P, (Sym2.toFinset e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ P, 2 :=
        Finset.sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split <;> omega)
    _ = 2 * P.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Per-source weight norm bound, inequality (I)** (GJ §17.6.1, brick F5a-1).
With `Mr` bounding the complex field base (`hMr : ‖Complex.tanh b‖ ≤ Mr`) and
`hMr1 : 1 ≤ Mr` (so `Mr = max(1, ‖Complex.tanh b‖)` is admissible),
`‖fieldSourceWeightℂ A a b S‖ ≤ Mr^{|A|}·(Mr²·|tanh a|)^{|S|}`.

Four-step proof: (a) factor the norm, `‖(tanh a : ℂ)‖ = |tanh a|`
(`Complex.norm_real`); (b) bound the field base by `Mr` (`pow_le_pow_left₀`,
base monotone); (c) `|∂S △ A| ≤ 2|S| + |A|` via inclusion `∂S △ A ⊆ ∂S ∪ A`
(`Finset.symmDiff_subset_union`, avoiding the subtractive `card_symmDiff`),
`Finset.card_union_le` and `oddBoundary_card_le_two_mul_card`; (d) inflate the
`Mr`-exponent using `1 ≤ Mr` (`pow_le_pow_right₀`, exponent monotone) and split
`Mr^{2|S|+|A|} = Mr^{|A|}·(Mr²)^{|S|}` (`pow_add`, `pow_mul`).  Field/source
analogue of `norm_fieldPolymerWeightℂ_le` (odd boundary replaced by
`∂S △ A`). -/
private theorem fieldSourceWeightℂ_norm_le (A : Finset ι) (a : ℝ) (b : ℂ)
    (S : Finset (Sym2 ι)) {Mr : ℝ} (hMr1 : 1 ≤ Mr) (hMr : ‖Complex.tanh b‖ ≤ Mr) :
    ‖fieldSourceWeightℂ A a b S‖ ≤ Mr ^ A.card * (Mr ^ 2 * |Real.tanh a|) ^ S.card := by
  have hcard : (oddBoundary S ∆ A).card ≤ 2 * S.card + A.card := by
    calc (oddBoundary S ∆ A).card
        ≤ (oddBoundary S ∪ A).card :=
          Finset.card_le_card Finset.symmDiff_subset_union
      _ ≤ (oddBoundary S).card + A.card := Finset.card_union_le _ _
      _ ≤ 2 * S.card + A.card := by
          have := oddBoundary_card_le_two_mul_card S; omega
  calc ‖fieldSourceWeightℂ A a b S‖
      = |Real.tanh a| ^ S.card * ‖Complex.tanh b‖ ^ (oddBoundary S ∆ A).card := by
        unfold fieldSourceWeightℂ
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |Real.tanh a| ^ S.card * ((Mr ^ 2) ^ S.card * Mr ^ A.card) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
        calc ‖Complex.tanh b‖ ^ (oddBoundary S ∆ A).card
            ≤ Mr ^ (oddBoundary S ∆ A).card :=
              pow_le_pow_left₀ (norm_nonneg _) hMr _
          _ ≤ Mr ^ (2 * S.card + A.card) := pow_le_pow_right₀ hMr1 hcard
          _ = (Mr ^ 2) ^ S.card * Mr ^ A.card := by rw [pow_add, pow_mul]
    _ = Mr ^ A.card * (Mr ^ 2 * |Real.tanh a|) ^ S.card := by rw [mul_pow]; ring

/-- **Per-source weight geometric bound, parametric-`κ` capstone** (GJ §17.6.1,
brick F5a-1).  With `hMr1 : 1 ≤ Mr`, `hMr : ‖Complex.tanh b‖ ≤ Mr` and
`hκ : 0 ≤ κ`,
`‖fieldSourceWeightℂ A a b S‖ · exp(κ·|polymerSupport S ∪ A|)
   ≤ Mr^{|A|}·exp(κ·|A|) · (Mr²·e^{2κ}·|tanh a|)^{|S|}`,
where `polymerSupport S ∪ A` is the F5-pre-2a avoiding collar.

Multiplies inequality (I) `fieldSourceWeightℂ_norm_le` by the collar `exp`-factor:
`|polymerSupport S ∪ A| ≤ 2|S| + |A|` (`polymerSupport_card_le_two_mul_card`,
`Finset.card_union_le`) and `0 ≤ κ` give
`exp(κ·|∂S ∪ A|) ≤ exp(κ·|A|)·(e^{2κ})^{|S|}` (`Real.exp_le_exp`,
`Real.exp_nat_mul`, `Real.exp_add`); combining the two `|S|`-powers
(`mul_pow`) yields the geometric ratio base `a₀ = Mr²·e^{2κ}·|tanh a|`.  This is
the self-contained brick that F5a-3 will instantiate at `κ = κ_Δ` (the
volume-uniform local KP constant), decoupled from the F5a-2 fiber count. -/
theorem fieldSourceWeightℂ_norm_mul_exp_le (A : Finset ι) (a : ℝ) (b : ℂ)
    (S : Finset (Sym2 ι)) {Mr κ : ℝ} (hMr1 : 1 ≤ Mr) (hMr : ‖Complex.tanh b‖ ≤ Mr)
    (hκ : 0 ≤ κ) :
    ‖fieldSourceWeightℂ A a b S‖ * Real.exp (κ * ((polymerSupport S ∪ A).card : ℝ))
      ≤ Mr ^ A.card * Real.exp (κ * (A.card : ℝ)) *
          (Mr ^ 2 * Real.exp (2 * κ) * |Real.tanh a|) ^ S.card := by
  have hMr0 : (0 : ℝ) ≤ Mr := le_trans zero_le_one hMr1
  have hw := fieldSourceWeightℂ_norm_le A a b S hMr1 hMr
  have hcoll : (polymerSupport S ∪ A).card ≤ 2 * S.card + A.card := by
    calc (polymerSupport S ∪ A).card
        ≤ (polymerSupport S).card + A.card := Finset.card_union_le _ _
      _ ≤ 2 * S.card + A.card := by
          have := polymerSupport_card_le_two_mul_card S; omega
  have he : Real.exp (κ * ((polymerSupport S ∪ A).card : ℝ))
      ≤ Real.exp (κ * (A.card : ℝ)) * Real.exp (2 * κ) ^ S.card := by
    calc Real.exp (κ * ((polymerSupport S ∪ A).card : ℝ))
        ≤ Real.exp (κ * ((2 * S.card + A.card : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcoll) hκ
      _ = Real.exp (κ * (A.card : ℝ)) * Real.exp (2 * κ) ^ S.card := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          push_cast
          ring
  calc ‖fieldSourceWeightℂ A a b S‖ *
          Real.exp (κ * ((polymerSupport S ∪ A).card : ℝ))
      ≤ (Mr ^ A.card * (Mr ^ 2 * |Real.tanh a|) ^ S.card) *
          (Real.exp (κ * (A.card : ℝ)) * Real.exp (2 * κ) ^ S.card) :=
        mul_le_mul hw he (Real.exp_nonneg _)
          (mul_nonneg (pow_nonneg hMr0 _)
            (pow_nonneg (mul_nonneg (pow_nonneg hMr0 2) (abs_nonneg _)) _))
    _ = Mr ^ A.card * Real.exp (κ * (A.card : ℝ)) *
          (Mr ^ 2 * Real.exp (2 * κ) * |Real.tanh a|) ^ S.card := by
        have hbase : Mr ^ 2 * Real.exp (2 * κ) * |Real.tanh a|
            = (Mr ^ 2 * |Real.tanh a|) * Real.exp (2 * κ) := by ring
        rw [hbase, mul_pow]; ring

end IsingModel
