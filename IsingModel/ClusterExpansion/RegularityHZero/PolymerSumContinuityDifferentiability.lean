import IsingModel.ClusterExpansion.Families.SandwichBounds

/-!
# Cluster expansion zero-field regularity (1/4): continuity and differentiability

Structural split (1/4) of `ClusterExpansion.RegularityHZero`.  This child holds the
lattice Ising polymer partition function `latticeIsingPolymerPartition` with its
non-negativity and `1 ≤ ·` bounds, the polymer activity simp lemmas, the continuity and
differentiability of the vertex-disjoint polymer-family sum in the activity variable `t`
and in `β` / `J` through the `tanh(β·J)` substitution, and the resulting continuity and
differentiability of the partition function at `h = 0`.  The real-analytic upgrades live
in the sibling `...RealAnalyticityCapstone`, the complex-analytic core in
`...ComplexAnalyticityCore`, and the complex zero-free balls in `...ComplexZeroFreeBalls`.
See the `ClusterExpansion.RegularityHZero` facade module for the full contents overview.
-/

namespace IsingModel

open Finset
open scoped Topology

/-- **Lattice Ising polymer partition function**: the polymer model
partition function `polymerPartition` evaluated at the universe of all
polymers in `G` with the canonical activity `tanh(β·J)^|P|`. This is
the polymer-decomposition reformulation of the FV (3.45) sum
`∑_{X ⊆ E, even} tanh(β·J)^|X|` modulo the connected-components
identification (proved in subsequent PRs). -/
noncomputable def latticeIsingPolymerPartition {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β J : ℝ) : ℝ :=
  polymerPartition G (allPolymers G) (polymerActivity (Real.tanh (β * J)))

/-- **Polymer activity at non-negative `t` is non-negative**: with
`t = tanh(β·J)`, this gives `0 ≤ tanh(β·J)^|P|` whenever `0 ≤ β·J`. -/
theorem polymerActivity_nonneg {ι : Type*} {t : ℝ} (ht : 0 ≤ t)
    (P : Finset (Sym2 ι)) : 0 ≤ polymerActivity t P := by
  unfold polymerActivity
  exact pow_nonneg ht _

/-- **Lattice Ising polymer partition function ≥ 1 under `0 ≤ β·J`**:
since `0 ≤ β·J` implies `0 ≤ tanh(β·J)`, the activity is non-negative
and the empty family contributes exactly 1. -/
theorem latticeIsingPolymerPartition_ge_one {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ latticeIsingPolymerPartition G β J := by
  have h_tanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  unfold latticeIsingPolymerPartition
  apply polymerPartition_ge_one G _
  intro P _
  exact polymerActivity_nonneg h_tanh_nn P

/-- **Polymer activity is `1` on the empty edge set** (since `t^0 = 1`). -/
@[simp]
theorem polymerActivity_empty (t : ℝ) :
    polymerActivity t (∅ : Finset (Sym2 ι)) = 1 := by
  unfold polymerActivity
  simp

/-- **VD polymer-family sum is continuous in `t`**: the sum
`∑_{Γ ∈ vdCompatiblePolymerFamilies G} ∏_{P ∈ Γ} t^|P|`
is a finite sum of finite products of monomials `t^|P|`, hence continuous
(and indeed polynomial) in `t : ℝ`. This is the foundation for the §18.6
analyticity of the polymer expansion in `tanh(β·J)`. -/
theorem vdPolymerFamilies_sum_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine continuous_finset_sum _ ?_
  intro Γ _
  refine continuous_finset_prod _ ?_
  intro P _
  exact continuous_id.pow _

/-- **VD polymer-family sum is differentiable in `t`**: as a finite sum
of finite products of monomials `t^|P|`, the polymer-family sum is a
polynomial in `t`, hence differentiable on all of `ℝ`. Strengthens
`vdPolymerFamilies_sum_continuous` from `Continuous` to `Differentiable`
and prepares the §18.6 analyticity statement. -/
theorem vdPolymerFamilies_sum_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    Differentiable ℝ (fun t : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card) := by
  refine Differentiable.fun_sum (fun Γ _ => ?_)
  refine Differentiable.fun_finset_prod (fun P _ => ?_)
  exact (differentiable_id (𝕜 := ℝ)).pow _

/-- **`Real.tanh` is continuous on `ℝ`** (project-local helper): derived
from `tanh = sinh / cosh` together with `Real.cosh > 0`. Mathlib does
not yet export `Real.continuous_tanh`, so we provide it here. -/
theorem continuous_real_tanh : Continuous Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.continuous_sinh.div Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **`Real.tanh` is differentiable on `ℝ`** (project-local helper):
derived from `tanh = sinh / cosh` together with `Real.cosh > 0` and
`Differentiable.div`. Mathlib does not yet export `Real.differentiable_tanh`. -/
theorem differentiable_real_tanh : Differentiable ℝ Real.tanh := by
  have h_eq : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x :=
    funext (fun x => Real.tanh_eq_sinh_div_cosh x)
  rw [h_eq]
  exact Real.differentiable_sinh.div Real.differentiable_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- **VD polymer-family sum is continuous in `β` (with `J` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is continuous in `J` (with `β` fixed)**:
composing Step 555 with continuity of `tanh` and multiplication. -/
theorem vdPolymerFamilies_sum_tanh_continuous_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  exact (vdPolymerFamilies_sum_continuous G).comp (continuous_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `β` (with `J` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.mul_const`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **VD polymer-family sum is differentiable in `J` (with `β` fixed)**:
chain-rule composition of Step 558 with `differentiable_real_tanh` and
`Differentiable.const_mul`. -/
theorem vdPolymerFamilies_sum_tanh_differentiable_J
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ =>
      ∑ Γ ∈ vdCompatiblePolymerFamilies G,
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) := by
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  exact (vdPolymerFamilies_sum_differentiable G).comp
    (differentiable_real_tanh.comp h_mul)

/-- **Partition function continuous in `β` (at `h = 0`) via polymer
expansion**: combines the §18.4 polymer-family identity (Step 548) with
the polymer-family sum continuity (Step 556) and continuity of
`cosh(β·J)^|E|` to obtain
`Continuous (fun β => partitionFunction G ⟨J, 0, β⟩)`.

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three β-continuous factors. -/
theorem partitionFunction_continuous_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Continuous (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Continuous (fun β : ℝ => β * J) :=
    continuous_id.mul continuous_const
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_beta G J)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function continuous in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_continuous_beta_h_zero` for the
coupling variable, again via the polymer-family identity. The general
form for non-zero `h` is `partitionFunction_continuous_J` in
`GibbsMeasure.lean`; this `_h_zero` version goes through the polymer
expansion and so will be the natural place to extend to higher
regularity (e.g. analyticity) in subsequent steps. -/
theorem partitionFunction_continuous_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Continuous (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Continuous (fun J : ℝ => β * J) :=
    continuous_const.mul continuous_id
  refine Continuous.mul ?_ (vdPolymerFamilies_sum_tanh_continuous_J G β)
  refine continuous_const.mul ?_
  exact (Real.continuous_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `β` (at `h = 0`) via polymer
expansion**: strengthens `partitionFunction_continuous_beta_h_zero` from
`Continuous` to `Differentiable ℝ`, using Step 559 plus differentiability
of `cosh(β·J)^|E|` (composition of `Real.differentiable_cosh` and
`Differentiable.mul_const`, raised to the power `|E|`).

The polymer expansion realises `Z(J,0,β) = 2^|ι| · cosh(β·J)^|E| ·
∑_Γ ∏_P tanh(β·J)^|P|` as a product of three differentiable factors. -/
theorem partitionFunction_differentiable_beta_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    Differentiable ℝ (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun β : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun β : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (partitionFunction_high_temp_expansion_h_zero_polymer_family G J)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun β : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).mul_const J
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_beta G J)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

/-- **Partition function differentiable in `J` (at `h = 0`) via polymer
expansion**: dual of `partitionFunction_differentiable_beta_h_zero` for
the coupling variable. Strengthens `partitionFunction_continuous_J_h_zero`
from `Continuous` to `Differentiable ℝ`. -/
theorem partitionFunction_differentiable_J_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    Differentiable ℝ (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) := by
  have h_eq : (fun J : ℝ => partitionFunction G ⟨J, 0, β⟩) =
      fun J : ℝ => (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ Γ ∈ vdCompatiblePolymerFamilies G,
          ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
    funext (fun J => partitionFunction_high_temp_expansion_h_zero_polymer_family G J β)
  rw [h_eq]
  have h_mul : Differentiable ℝ (fun J : ℝ => β * J) :=
    (differentiable_id (𝕜 := ℝ)).const_mul β
  refine Differentiable.mul ?_ (vdPolymerFamilies_sum_tanh_differentiable_J G β)
  refine (differentiable_const _).mul ?_
  exact (Real.differentiable_cosh.comp h_mul).pow _

end IsingModel
