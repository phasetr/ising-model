import IsingModel.ClusterExpansion.FieldSourceWeightBound
import IsingModel.ClusterExpansion.FieldSourceCount
import IsingModel.ClusterExpansion.FieldSourcePeel
import IsingModel.ClusterExpansion.FieldVertexAvoidingRatio
import IsingModel.ClusterExpansion.GeometricFiberSum
import IsingModel.Conditioning.CorrelationClosed.GeneralFieldClosedComplex

/-!
# Volume-uniform complex field correlation bound (GJ §17.6.1, brick F5a-3)

This file assembles the volume-uniform bound on the complex-`h` field correlation
`fieldCorrelationℂ G A a b`, the field (`∂/∂h`) analogue of the convergent
cluster-expansion two-point ratio bound `twoPointRatio_norm_le_geometric`
(`TwoPointRatioBound.lean`).  It is a **pure assembly** of already-proved
inequalities — no new analytic content beyond F5a-1
(`fieldSourceWeightℂ_norm_mul_exp_le`), F5a-2b
(`fieldSourceConfigsOfCard_card_le`), F5-pre-2a
(`fieldPolymerZℂ_GavoidVertex_div_norm_le_exp`), and the geometric-sum kernel
`sum_le_geometric_closed_of_fiber_card_le`.

## The three stages
* **Stage 0** (`fieldCorrelationℂ_eq_sum_source_ratio`): the algebraic identity
  writing the correlation as a source-configuration sum of marked weights times
  per-source avoiding-graph partition ratios.  Unconditional (the field
  convention `x / 0 = 0` makes `Finset.sum_div` need no non-vanishing hypothesis).
* **Stage a** (`fieldSourceWeight_mul_ratio_norm_le`): the term-wise bound
  `‖w(S)‖·‖ratio_S‖ ≤ A₀·a₀^{|S|}` from F5-pre-2a and F5a-1.
* **Stage b+c** (`fieldCorrelationℂ_norm_le_uniform`): the geometric closure
  `‖fieldCorrelationℂ‖ ≤ A₀/(1-q)` under the field-specific window `q < 1`.

## Constants (all volume-free)
With `κ_Δ = fieldCEKappaDelta G a b` the volume-uniform local Kotecký–Preiss
exponent of F5-pre-2a and `M = max 1 ‖Complex.tanh b‖`,
`A₀ = M^{|A|}·e^{κ_Δ|A|}`, `a₀ = M²·e^{2κ_Δ}·|tanh a|`, `B = 2^{|A|}·Δ²`
(`Δ = G.maxDegree`) and `q = a₀·B`.  Every factor depends only on
`(Δ, a, b, |A|)` — the vertex/degree data — never on the vertex count `|ι|`, so
the bound is `|ι|`-independent for each fixed graph.  It is uniform along an
exhaustion precisely when `Δ = G.maxDegree` stays bounded along it: for a lattice
exhaustion `Δ = 2d` is constant, so the constants freeze and the bound is
genuinely exhaustion-uniform (the property F5b/F6 build on).

References: Friedli–Velenik §5.4, Theorem 5.4, p. 224, is the convergence
source; Kotecký–Preiss Theorem 1 supplies only the abstract convergence
criterion. Glimm–Jaffe §18.3, Theorem 18.3.1, eq. (18.3.3), p. 330, is a
continuum P(φ)₂ analogy only; not a lattice-Ising source. This uniform bound is
a project extension.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The volume-uniform local Kotecký–Preiss exponent** (GJ §17.6.1, brick F5a-3).
This is the coefficient `κ_Δ` appearing in the F5-pre-2a avoiding-ratio bound
`fieldPolymerZℂ_GavoidVertex_div_norm_le_exp`, namely
`κ_Δ = (1-r_∗)⁻¹·((1 - 8 r_∗/(1-r_∗)²)⁻¹)²` with `r_∗ = Δ²·e·(M²·|tanh a|)`,
`M = max 1 ‖Complex.tanh b‖`, `Δ = G.maxDegree`.  It depends only on
`(Δ, a, b)`, never on the vertex count, and is definitionally equal to the
literal exponent produced by F5-pre-2a. -/
noncomputable def fieldCEKappaDelta (G : SimpleGraph ι) [DecidableRel G.Adj]
    (a : ℝ) (b : ℂ) : ℝ :=
  (1 / (1 - (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
    * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2

/-- **Stage 0: source-ratio identity** (GJ §17.6.1, brick F5a-3).  The complex
field correlation is the source-configuration sum of marked source weights times
per-source avoiding-graph partition ratios:
`fieldCorrelationℂ G A a b
  = ∑_{S ∈ fieldSourceConfigs G A} w(S)·(Z^f(GavoidVertex G (∂S ∪ A))/Z^f(G))`.
Source peel (`fieldTwoPointNumℂ_eq_sum_source_avoid`) plus the empty-source
denominator bridge (`fieldTwoPointNumℂ_empty_eq_fieldPolymerZℂ`),
`Finset.sum_div` and `mul_div_assoc`.  **Unconditional**: `Finset.sum_div` holds
in a field with the convention `x / 0 = 0`, so no `Z^f(G) ≠ 0` hypothesis is
needed. -/
private theorem fieldCorrelationℂ_eq_sum_source_ratio (G : SimpleGraph ι)
    [Fintype G.edgeSet] (A : Finset ι) (a : ℝ) (b : ℂ) :
    fieldCorrelationℂ G A a b
      = ∑ S ∈ fieldSourceConfigs G A, fieldSourceWeightℂ A a b S *
          (fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b /
            fieldPolymerZℂ G a b) := by
  unfold fieldCorrelationℂ
  rw [fieldTwoPointNumℂ_eq_sum_source_avoid, fieldTwoPointNumℂ_empty_eq_fieldPolymerZℂ,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [mul_div_assoc]

/-- **Stage a: per-source geometric term bound** (GJ §17.6.1, brick F5a-3).  For
every source configuration `S`, the marked source weight times the per-source
avoiding-graph partition ratio is bounded by the geometric term `A₀·a₀^{|S|}`:
`‖w(S)‖·‖Z^f(GavoidVertex G (∂S ∪ A))/Z^f(G)‖
   ≤ M^{|A|}·e^{κ_Δ|A|}·(M²·e^{2κ_Δ}·|tanh a|)^{|S|}`,
`M = max 1 ‖Complex.tanh b‖`.  The avoiding ratio is bounded by
`e^{κ_Δ·|∂S ∪ A|}` (F5-pre-2a, `fieldPolymerZℂ_GavoidVertex_div_norm_le_exp`, at
the collar `W = polymerSupport S ∪ A`), and F5a-1
(`fieldSourceWeightℂ_norm_mul_exp_le` with `κ := κ_Δ`, `Mr := M`) collapses the
product to the geometric term.  The `Mr := M` here is the **pointwise** value at
`b`, distinct from the ball-uniform F5-pre-2a parameter `Mrb`. -/
private theorem fieldSourceWeight_mul_ratio_norm_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (A : Finset ι) {a Awin r Mrb ρ : ℝ} {b : ℂ}
    (S : Finset (Sym2 ι))
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mrb)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mrb) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    ‖fieldSourceWeightℂ A a b S‖ *
        ‖fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b /
          fieldPolymerZℂ G a b‖
      ≤ (max 1 ‖Complex.tanh b‖) ^ A.card *
            Real.exp (fieldCEKappaDelta G a b * (A.card : ℝ)) *
          ((max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
              |Real.tanh a|) ^ S.card := by
  -- `0 ≤ κ_Δ`: the local KP exponent is a product of a nonnegative reciprocal and a square.
  have htanh_le : |Real.tanh a| ≤ ρ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact le_of_lt (lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA)
  have hDa1 : (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1 := by
    refine lt_of_le_of_lt ?_ hkp
    gcongr
  have hκ : 0 ≤ fieldCEKappaDelta G a b := by
    unfold fieldCEKappaDelta
    refine mul_nonneg (one_div_nonneg.mpr ?_) (sq_nonneg _)
    linarith
  -- F5-pre-2a: the avoiding ratio at the collar `W = polymerSupport S ∪ A`.
  have hratio := fieldPolymerZℂ_GavoidVertex_div_norm_le_exp G (polymerSupport S ∪ A)
    ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp hρwin
  calc ‖fieldSourceWeightℂ A a b S‖ *
          ‖fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b /
            fieldPolymerZℂ G a b‖
      ≤ ‖fieldSourceWeightℂ A a b S‖ *
          Real.exp (fieldCEKappaDelta G a b * ((polymerSupport S ∪ A).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ ≤ (max 1 ‖Complex.tanh b‖) ^ A.card *
            Real.exp (fieldCEKappaDelta G a b * (A.card : ℝ)) *
          ((max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
              |Real.tanh a|) ^ S.card :=
        fieldSourceWeightℂ_norm_mul_exp_le A a b S (le_max_left 1 _) (le_max_right 1 _) hκ

/-- **Volume-uniform complex field correlation bound** (GJ §17.6.1, brick F5a-3,
capstone; TeX §sec:f5a3).  On the F5-pre-2a field degree window (target coupling
`a ∈ Set.Ico 0 Awin`, field `b` in the `π/2`-ball `Metric.ball 0 r` with a
ball-uniform bound `Mrb`, degree-window hypotheses `hkp`, `hρwin`), and under the
**field-specific window** `hq : q < 1` with
`q = M²·e^{2κ_Δ}·|tanh a|·(2^{|A|}·Δ²)`, `M = max 1 ‖Complex.tanh b‖`,
`κ_Δ = fieldCEKappaDelta G a b`, `Δ = G.maxDegree`,
\[
  \bigl\|\mathrm{fieldCorrelation}^{\mathbb C}\,G\,A\,a\,b\bigr\|
    \;\le\; \frac{A_0}{1-q},\qquad A_0 = M^{|A|}\,e^{\kappa_\Delta|A|}.
\]
The bound is **volume-uniform** (`A₀`, `a₀`, `B` depend only on `Δ, a, b, |A|`,
never on `|ι|`), the field (`∂/∂h`) analogue of `twoPointRatio_norm_le_geometric`.
This is a **pointwise-in-`b`** bound; it is the per-point ingredient towards the
`hbdd` datum of the Vitali/Montel brick F6, but F6's ball-uniform `hbdd` requires
in addition a `b`-uniform control of `κ_Δ = fieldCEKappaDelta G a b` over the
`π/2`-ball (supplied separately), which this capstone does not by itself provide.
Assembly: Stage 0
(`fieldCorrelationℂ_eq_sum_source_ratio`) + `norm_sum_le`/`norm_mul` reduce the
norm to a source sum; Stage a (`fieldSourceWeight_mul_ratio_norm_le`) bounds each
term by `A₀·a₀^{|S|}`; F5a-2b (`fieldSourceConfigsOfCard_card_le`) supplies the
`(2^{|A|}Δ²)^ℓ` fiber count; and `sum_le_geometric_closed_of_fiber_card_le` closes
the geometric series under `hq`.  The window `hq` is an **independent** field
hypothesis (not implied by the degree window `hkp`/`hρwin`). -/
theorem fieldCorrelationℂ_norm_le_uniform (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] (A : Finset ι)
    {a Awin r Mrb ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 Awin) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mrb)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mrb) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh Awin < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1)
    (hq : (max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
          |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) < 1) :
    ‖fieldCorrelationℂ G A a b‖
      ≤ (max 1 ‖Complex.tanh b‖) ^ A.card *
            Real.exp (fieldCEKappaDelta G a b * (A.card : ℝ)) /
          (1 - (max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) *
              |Real.tanh a| * (2 ^ A.card * (G.maxDegree : ℝ) ^ 2)) := by
  classical
  have hM0 : (0 : ℝ) ≤ max 1 ‖Complex.tanh b‖ := le_trans zero_le_one (le_max_left _ _)
  -- Stage 0 + `norm_sum_le`/`norm_mul`: the norm is bounded by the source sum.
  have hnorm : ‖fieldCorrelationℂ G A a b‖
      ≤ ∑ S ∈ fieldSourceConfigs G A,
          ‖fieldSourceWeightℂ A a b S‖ *
            ‖fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b /
              fieldPolymerZℂ G a b‖ := by
    rw [fieldCorrelationℂ_eq_sum_source_ratio]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun S _ => ?_)
    rw [norm_mul]
  refine hnorm.trans ?_
  -- Stage b+c: apply the geometric fiber-count closure.
  refine sum_le_geometric_closed_of_fiber_card_le
    (fieldSourceConfigs G A) (fun S => S.card)
    (fun S => ‖fieldSourceWeightℂ A a b S‖ *
      ‖fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b / fieldPolymerZℂ G a b‖)
    ((max 1 ‖Complex.tanh b‖) ^ A.card * Real.exp (fieldCEKappaDelta G a b * (A.card : ℝ)))
    ((max 1 ‖Complex.tanh b‖) ^ 2 * Real.exp (2 * fieldCEKappaDelta G a b) * |Real.tanh a|)
    (2 ^ A.card * (G.maxDegree : ℝ) ^ 2) G.edgeFinset.card ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq
  · -- sizes are at most the number of edges
    intro S hS
    rw [fieldSourceConfigs, Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.card_le_card hS.1
  · -- nonnegativity of the weights
    intro S _
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · -- per-source geometric term bound (Stage a)
    intro S _
    exact fieldSourceWeight_mul_ratio_norm_le G A S ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp hρwin
  · -- volume-uniform fiber count `(2^{|A|}Δ²)^n` (F5a-2b)
    intro n
    have hc := fieldSourceConfigsOfCard_card_le (G := G) A n
    have hcast : (((fieldSourceConfigs G A).filter (fun S => S.card = n)).card : ℝ)
        ≤ (((2 ^ A.card * G.maxDegree ^ 2) ^ n : ℕ) : ℝ) := by exact_mod_cast hc
    refine hcast.trans (le_of_eq ?_)
    push_cast
    ring
  · -- `0 ≤ A₀`
    exact mul_nonneg (pow_nonneg hM0 _) (Real.exp_nonneg _)
  · -- `0 ≤ a₀`
    exact mul_nonneg (mul_nonneg (pow_nonneg hM0 2) (Real.exp_nonneg _)) (abs_nonneg _)
  · -- `0 ≤ B`
    positivity

end IsingModel
