import IsingModel.ClusterExpansion.FieldMayerIdentity
import IsingModel.ClusterExpansion.SourceGeneratingFunction
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Field polymer `exp` identity, real-`h` non-vanishing, and the complex-`h` prelude
(GJ §17.6.1, brick 5)

Brick 5 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1 (`∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).  Brick 4 (`FieldMayerIdentity.lean`) gave the
algebraic Mayer–Montroll **log**-identity
`fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b` at real `h`.
This file converts that log-identity into an **exponential** identity and the
associated **non-vanishing** of the field polymer partition function, the
transition point of the route into complex `h`:

* `fieldPolymerZ G a b > 0` at real `h` (via `= 1 + ε`, `|ε| < 1`);
* `Real.exp (fieldPolymerFreeEnergy G a b) = fieldPolymerZ G a b`;
* `fieldPolymerZ G a b ≠ 0` (`exp`-image, the phrasing that generalises to `ℂ`);
* `fieldPolymerZ G a b = Real.exp (∑' n, fieldMayerExpansionTerm G n a b)`.

The real-`h` half is an `exp ∘ log` round-trip; its role is to pin the partition
function as "`exp` of a convergent Mayer series", from which `≠ 0` is automatic
(`exp` never vanishes).  We additionally supply the **complex-`h` prelude**: the
type design of the complex field weight
`w^ℂ_{a,b}(P) = tanh(a)^|P| · Complex.tanh(b)^{#odd(P)}` (`b ∈ ℂ`), its agreement
with the real weight on the real `b`-axis, and the `M²`-inflated dominating
activity (`M = max(1, ‖Complex.tanh b‖)`) that will carry the complex
non-vanishing in brick 6.  The combinatorial input is the parity bound
`#odd(P) ≤ 2·|P|` (an edge set covers at most `2·|P|` vertices), proved here as a
universal lemma.  Honest scope: brick 5 supplies the real-`h` `exp`/non-vanishing
and the complex **type/estimate** design only; the complex `Z_ℂ ≠ 0` body is
brick 6, the Montel/Vitali re-plumbing is brick 7, and brick 8/F6c is the
small-coupling holomorphic local-limit endpoint, with equality at one field value
`b₀`.  This brick does not export a real infinite-volume `HasDerivAt`.  The
downstream `FieldCorrelationInfiniteFieldDeriv.lean` derives real
differentiability only for normalized `⟨a, b, 1⟩`, small `a`, and
`0 < b < r < π/2`; the endpoint, full-range, series, sign, and uniform-bound
questions remain outside that capstone.

## References
- Friedli–Velenik §5.4, Theorem 5.4, p. 224, gives convergence; Exercise 5.8,
  p. 238, with its Appendix C solution, p. 531, gives the exact real-field setup.
  The complex-field `exp` identity and non-vanishing are project extensions.
- Glimm–Jaffe §18.5, Theorem 18.5.1, p. 335, is a continuum P(φ)₂ analogy only;
  not a lattice-Ising source.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Real-`h` positivity, `exp` identity, and non-vanishing -/

/-- **Real-`h` positivity of the field polymer partition function**: under the
brick-4 smallness hypothesis `|ε_{a,b}| < 1` (`h_abs`), `0 < fieldPolymerZ G a b`.
Since `fieldPolymerZ G a b = 1 + ε_{a,b}` (`fieldPolymerZ_eq_one_add`) and
`|ε_{a,b}| < 1` gives `ε_{a,b} > -1`, we get `1 + ε_{a,b} > 0`.  The `h = 0`
"every monomial `≥ 0`, so sum `≥ 1`" route does **not** transfer: the field weight
`tanh(a)^|P|·tanh(b)^{#odd(P)}` can be negative, so the `1 + ε > 0` argument is
mandatory. -/
theorem fieldPolymerZ_pos (G : SimpleGraph ι) [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1) :
    0 < fieldPolymerZ G a b := by
  rw [fieldPolymerZ_eq_one_add]
  have hgt := (abs_lt.mp h_abs).1
  linarith

/-- **`exp` of the field polymer free energy recovers the partition function**:
under `|ε_{a,b}| < 1`, `Real.exp (fieldPolymerFreeEnergy G a b) = fieldPolymerZ G a b`.
Since `fieldPolymerFreeEnergy = Real.log (fieldPolymerZ)`, this is `Real.exp_log`
applied to the positivity `fieldPolymerZ_pos`. -/
theorem exp_fieldPolymerFreeEnergy (G : SimpleGraph ι) [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1) :
    Real.exp (fieldPolymerFreeEnergy G a b) = fieldPolymerZ G a b := by
  rw [fieldPolymerFreeEnergy]
  exact Real.exp_log (fieldPolymerZ_pos G h_abs)

/-- **Real-`h` non-vanishing of the field polymer partition function**: under
`|ε_{a,b}| < 1`, `fieldPolymerZ G a b ≠ 0`.  Phrased via the `exp`-image
(`= Real.exp (fieldPolymerFreeEnergy)` and `Real.exp_ne_zero`) rather than via
`ne_of_gt`, so that the argument mirrors the complex non-vanishing of brick 6. -/
theorem fieldPolymerZ_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1) :
    fieldPolymerZ G a b ≠ 0 := by
  rw [← exp_fieldPolymerFreeEnergy G h_abs]
  exact Real.exp_ne_zero _

/-- **Field polymer partition function as `exp` of the Mayer series** (GJ §17.6.1,
brick 5): under the two brick-4 convergence hypotheses `|ε_{a,b}| < 1` (`h_abs`)
and `e·A_C < 1` (`hact`, `A_C = ∑_P |tanh a|^|P|`),
`fieldPolymerZ G a b = Real.exp (∑' n, fieldMayerExpansionTerm G n a b)`.  Combines
`exp_fieldPolymerFreeEnergy` with the brick-4 Mayer–Montroll capstone
`field_mayer_identity_general`.  This is the field mirror of the `h = 0` identity
`∑_Γ ∏ t^|P| = exp (∑_n' mayerExpansionTerm)` inside
`vdPolymerFamilies_sum_pow_eq_exp_tsum_mayerExpansionTermComplex`. -/
theorem fieldPolymerZ_eq_exp_tsum_fieldMayerExpansionTerm (G : SimpleGraph ι)
    [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    fieldPolymerZ G a b = Real.exp (∑' n, fieldMayerExpansionTerm G n a b) := by
  rw [← exp_fieldPolymerFreeEnergy G h_abs, field_mayer_identity_general G h_abs hact]

/-! ## The complex-`h` prelude: types, real-axis agreement, dominating estimate -/

/-- **Complex field polymer weight** `w^ℂ_{a,b}(P) = (tanh a : ℂ)^|P| ·
(Complex.tanh b)^{#odd(P)}`, the complex mirror of `fieldPolymerWeight` with the
field parameter `b` made complex (the coupling `a` stays real).  The
`#odd(P) = (oddBoundary P).card` factor reuses the odd-degree vertex set
`oddBoundary` (`SourceGeneratingFunction.lean`), definitionally the same filter
used by `fieldPolymerWeight`.  `Complex.tanh` is meromorphic, with poles at
`(2k+1)πi/2`; when `#odd(P) > 0`, the weight is analytic in `b` only on pole-free
neighbourhoods such as the ball used later (apart from a trivial zero coupling
prefactor).  When `#odd(P) = 0`, the field factor is `1`, so the weight is a
constant polynomial in `b`. -/
noncomputable def fieldPolymerWeightℂ (a : ℝ) (b : ℂ) (P : Finset (Sym2 ι)) : ℂ :=
  (Real.tanh a : ℂ) ^ P.card * (Complex.tanh b) ^ (oddBoundary P).card

/-- **Complex field polymer partition function**
`fieldPolymerZℂ G a b := ∑_{Γ ∈ vdConnectedPolymerFamilies G} ∏_{P ∈ Γ} w^ℂ_{a,b}(P)`,
the complex mirror of `fieldPolymerZ`.  Continued only in `b ∈ ℂ` (the coupling
`a` stays real, matching Theorem 17.6.1's `∂/∂h`); the complex `exp` identity and
`≠ 0` on the Kotecký–Preiss ball are deferred to brick 6. -/
noncomputable def fieldPolymerZℂ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a : ℝ) (b : ℂ) : ℂ :=
  ∑ Γ ∈ vdConnectedPolymerFamilies G, ∏ P ∈ Γ, fieldPolymerWeightℂ a b P

/-- **Real-axis agreement of the complex field weight**: for real `b`,
`fieldPolymerWeightℂ a (b : ℂ) P = (fieldPolymerWeight a b P : ℂ)`.  Both sides
unfold to `tanh(a)^|P|·tanh(b)^{#odd(P)}`; the cast is pushed through the product
and the powers, using `Complex.ofReal_tanh : (Real.tanh x : ℂ) = Complex.tanh x`. -/
theorem fieldPolymerWeightℂ_ofReal (a b : ℝ) (P : Finset (Sym2 ι)) :
    fieldPolymerWeightℂ a (b : ℂ) P = (fieldPolymerWeight a b P : ℂ) := by
  unfold fieldPolymerWeightℂ fieldPolymerWeight oddBoundary
  push_cast [Complex.ofReal_tanh]
  ring

/-- **Real-axis agreement of the complex field partition function**: for real `b`,
`fieldPolymerZℂ G a (b : ℂ) = (fieldPolymerZ G a b : ℂ)`.  The cast distributes
over the family sum and the polymer product, and each factor agrees by
`fieldPolymerWeightℂ_ofReal`.  This supplies the real-`b`-axis values that brick 6
will feed to the analytic-continuation identity theorem. -/
theorem fieldPolymerZℂ_ofReal (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ) :
    fieldPolymerZℂ G a (b : ℂ) = (fieldPolymerZ G a b : ℂ) := by
  unfold fieldPolymerZℂ fieldPolymerZ
  push_cast
  exact Finset.sum_congr rfl
    (fun Γ _ => Finset.prod_congr rfl (fun P _ => fieldPolymerWeightℂ_ofReal a b P))

/-- **Parity bound `#odd(P) ≤ 2·|P|`**: the odd-degree vertex set of a polymer `P`
(a set of `|P|` edges) has at most `2·|P|` elements.  Every odd-degree vertex lies
on some edge of `P` (odd degree is positive), so `oddBoundary P ⊆ ⋃_{e ∈ P} e`, and
each edge `e` contributes at most `2` vertices (`Sym2.card_toFinset ≤ 2`).  A
universal lemma (no even-degree hypothesis, unlike
`polymerSupport_card_le_card_of_mem_allPolymers`), needed for the complex
dominating estimate. -/
theorem oddBoundary_card_le_two_mul_card (P : Finset (Sym2 ι)) :
    (oddBoundary P).card ≤ 2 * P.card := by
  classical
  have hsub : oddBoundary P ⊆ P.biUnion Sym2.toFinset := by
    intro v hv
    rw [oddBoundary, Finset.mem_filter] at hv
    obtain ⟨_, hodd⟩ := hv
    have hpos : 0 < (P.filter (v ∈ ·)).card := by
      rcases hodd with ⟨m, hm⟩; omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at he
    exact Finset.mem_biUnion.mpr ⟨e, he.1, Sym2.mem_toFinset.mpr he.2⟩
  calc (oddBoundary P).card
      ≤ (P.biUnion Sym2.toFinset).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ P, (Sym2.toFinset e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ P, 2 :=
        Finset.sum_le_sum (fun e _ => by rw [Sym2.card_toFinset]; split <;> omega)
    _ = 2 * P.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **`M²`-inflated pointwise majorant of the complex field weight**: with
`M = max(1, ‖Complex.tanh b‖)`,
`‖fieldPolymerWeightℂ a b P‖ ≤ (M² · |tanh a|)^|P|`.  Since `‖Complex.tanh b‖`
need not be `≤ 1` at complex `b`, the naive real bound fails; using `M ≥ 1`,
`‖Complex.tanh b‖^{#odd(P)} ≤ M^{#odd(P)} ≤ M^{2|P|} = (M²)^{|P|}` via the parity
bound `oddBoundary_card_le_two_mul_card`.  This is the key estimate feeding the
complex Kotecký–Preiss window of brick 6. -/
theorem norm_fieldPolymerWeightℂ_le (a : ℝ) (b : ℂ) (P : Finset (Sym2 ι)) :
    ‖fieldPolymerWeightℂ a b P‖ ≤
      ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ P.card := by
  set M := max 1 ‖Complex.tanh b‖ with hM
  calc ‖fieldPolymerWeightℂ a b P‖
      = |Real.tanh a| ^ P.card * ‖Complex.tanh b‖ ^ (oddBoundary P).card := by
        unfold fieldPolymerWeightℂ
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |Real.tanh a| ^ P.card * (M ^ 2) ^ P.card := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
        calc ‖Complex.tanh b‖ ^ (oddBoundary P).card
            ≤ M ^ (oddBoundary P).card :=
              pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
          _ ≤ M ^ (2 * P.card) :=
              pow_le_pow_right₀ (le_max_left _ _) (oddBoundary_card_le_two_mul_card P)
          _ = (M ^ 2) ^ P.card := by rw [pow_mul]
    _ = (M ^ 2 * |Real.tanh a|) ^ P.card := by rw [mul_pow]; ring

/-- **`M²`-inflated aggregate majorant of the complex field partition function**:
with `M = max(1, ‖Complex.tanh b‖)`,
`‖fieldPolymerZℂ G a b‖ ≤ ∑_{Γ} ∏_{P ∈ Γ} (M² · |tanh a|)^|P|`.  Lifts the
pointwise bound `norm_fieldPolymerWeightℂ_le` through the family sum
(`norm_sum_le`) and the polymer product (`norm_prod_le`, `Finset.prod_le_prod`).
The right-hand side is the real connected-species gas at the inflated activity
`t_* = M²·|tanh a|`; its Kotecký–Preiss summability window is deferred to
brick 6. -/
theorem norm_fieldPolymerZℂ_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a : ℝ) (b : ℂ) :
    ‖fieldPolymerZℂ G a b‖ ≤
      ∑ Γ ∈ vdConnectedPolymerFamilies G,
        ∏ P ∈ Γ, ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ P.card := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun Γ _ => ?_))
  calc ‖∏ P ∈ Γ, fieldPolymerWeightℂ a b P‖
      ≤ ∏ P ∈ Γ, ‖fieldPolymerWeightℂ a b P‖ := norm_prod_le _ _
    _ ≤ ∏ P ∈ Γ, ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ^ P.card :=
        Finset.prod_le_prod (fun P _ => norm_nonneg _)
          (fun P _ => norm_fieldPolymerWeightℂ_le a b P)

end IsingModel
