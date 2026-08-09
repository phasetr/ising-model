import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.PseudoMass.FromParamsBasic.BasicSlices

/-!
# ℤ^d exponential decay of the truncated two-point function, and the lattice mass

Defines, for `IsingModel.latticeGraph d` and an arbitrary `Ambient.Exhaustion` of
`Fin d → ℤ`, the predicate that the infinite-volume truncated two-point function at distinct
sites is dominated by a non-negative constant times `exp (-α * latticeDistance d i j)`, and
the lattice mass as the supremum in `ENNReal` of the non-negative rates satisfying it. The
predicate holds at every rate at zero inverse temperature with no hypothesis, and at zero
coupling under the ferromagnetic condition on the parameter record; it is antitone in the
rate; and at a strictly positive rate it implies the cluster property. The lattice mass is
non-negative unconditionally, is bounded below by any validating non-negative rate, and is
strictly positive as soon as some validating rate is strictly positive. The lower bound and
the positivity are recorded again for the concrete pair pseudo-mass at zero external field,
on the assumption that it validates the decay predicate, positivity additionally requiring
the pseudo-mass itself to be positive.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **Exponential decay of the ∞-volume Ursell 2-point function**:
on `latticeGraph d`, there exists a constant `C ≥ 0` such that
for every basepoint pair `(i, j)` with `i ≠ j`, the truncated
2-point function is bounded above (in absolute value) by
`C · exp(-α · latticeDistance d i j)`. The decay rate parameter
`α` plays the role of the inverse correlation length / mass
(see GJ §17.1 (17.1.5)); the physically meaningful regime is
`0 ≤ α`, but the predicate as stated does not impose this
condition (negative `α` corresponds to allowed exponential
*growth*, which the truncated 2-point function does satisfy
trivially since it is bounded). -/
def HasExponentialDecay
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin d → ℤ, i ≠ j →
    |truncated2Infinite (IsingModel.latticeGraph d) Λ p i j|
      ≤ C * Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ))

/-- **Trivial slice at `β = 0`**: at infinite temperature, the
∞-volume Ursell 2-point function vanishes identically, so the
exponential decay predicate holds for any rate `α` with witness
`C = 0`. No ferromagnetic hypothesis required. -/
theorem HasExponentialDecay_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h α : ℝ) :
    HasExponentialDecay d Λ (⟨J, h, 0⟩ : IsingParams ℝ) α := by
  refine ⟨0, le_refl _, fun i j _ => ?_⟩
  rw [truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j,
    abs_zero, zero_mul]

/-- **Trivial slice at `J = 0` (ferromagnetic)**: at zero coupling
with `0 ≤ h, 0 < β`, the ∞-volume Ursell 2-point function
vanishes off-diagonally (`truncated2Infinite_J_zero_of_ne`); the
predicate's `i ≠ j` restriction matches, so `C = 0` witnesses
the bound for any rate `α`. -/
theorem HasExponentialDecay_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β α : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    HasExponentialDecay d Λ (⟨0, h, β⟩ : IsingParams ℝ) α := by
  refine ⟨0, le_refl _, fun i j hij => ?_⟩
  rw [truncated2Infinite_J_zero_of_ne (IsingModel.latticeGraph d) Λ h β hf hij,
    abs_zero, zero_mul]

/-- **α-monotonicity**: if `α' ≤ α` and the predicate holds at
rate `α`, then it holds at rate `α'` with the same constant.
Decreasing the decay rate weakens the bound (`exp(-α' · dist) ≥
exp(-α · dist)` since `dist ≥ 0`). -/
theorem HasExponentialDecay_mono
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {α α' : ℝ} (hαα' : α' ≤ α)
    (h : HasExponentialDecay d Λ p α) :
    HasExponentialDecay d Λ p α' := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun i j hij => ?_⟩
  refine (hbound i j hij).trans ?_
  have hdist : (0 : ℝ) ≤ (IsingModel.latticeDistance d i j : ℝ) :=
    Nat.cast_nonneg _
  have hexp : Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ))
      ≤ Real.exp (-α' * (IsingModel.latticeDistance d i j : ℝ)) := by
    apply Real.exp_monotone
    have : -α * (IsingModel.latticeDistance d i j : ℝ)
        ≤ -α' * (IsingModel.latticeDistance d i j : ℝ) := by
      have hneg : -α ≤ -α' := neg_le_neg hαα'
      exact mul_le_mul_of_nonneg_right hneg hdist
    exact this
  exact mul_le_mul_of_nonneg_left hexp hC

/-- **Exponential decay implies cluster property**: for `α > 0`,
`HasExponentialDecay d Λ p α` implies `clusterProperty (latticeGraph d) Λ p`
(PR #792's predicate). The proof composes
`tendsto_latticeDistance_atTop_cofinite` (PR #782) with
`Real.tendsto_exp_atBot` to obtain
`(j ↦ C · exp(-α · latticeDistance d i j)) → 0` along `cofinite`,
then squeezes the truncated 2-point function via the bound. -/
theorem clusterProperty_latticeGraph_of_HasExponentialDecay
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {α : ℝ} (hα : 0 < α)
    (h : HasExponentialDecay d Λ p α) :
    clusterProperty (IsingModel.latticeGraph d) Λ p := by
  obtain ⟨C, hC, hbound⟩ := h
  intro i
  -- Step 1: g(j) := C * exp(-α * latticeDistance d i j) tends to 0 along cofinite.
  have hdist_nat : Filter.Tendsto
      (fun j : Fin d → ℤ => IsingModel.latticeDistance d i j)
      Filter.cofinite Filter.atTop :=
    IsingModel.tendsto_latticeDistance_atTop_cofinite d i
  have hdist_real : Filter.Tendsto
      (fun j : Fin d → ℤ => (IsingModel.latticeDistance d i j : ℝ))
      Filter.cofinite Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hdist_nat
  have hexp_atTop : Filter.Tendsto (fun x : ℝ => Real.exp (-α * x))
      Filter.atTop (nhds 0) := by
    have h_alpha_x : Filter.Tendsto (fun x : ℝ => α * x) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop hα
    have h_exp_neg : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have heq : (fun x : ℝ => Real.exp (-α * x))
        = (fun y : ℝ => Real.exp (-y)) ∘ (fun x : ℝ => α * x) := by
      funext x; simp [neg_mul]
    rw [heq]
    exact h_exp_neg.comp h_alpha_x
  have hg_const : Filter.Tendsto (fun x : ℝ => C * Real.exp (-α * x))
      Filter.atTop (nhds 0) := by
    have := hexp_atTop.const_mul C
    simpa using this
  have hg : Filter.Tendsto
      (fun j : Fin d → ℤ =>
        C * Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ)))
      Filter.cofinite (nhds 0) :=
    hg_const.comp hdist_real
  -- Step 2: |U_2(i, j)| ≤ g(j) eventually (avoiding the singleton {i}).
  have hbound_pos : ∀ᶠ (j : Fin d → ℤ) in Filter.cofinite,
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j
        ≤ C * Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ)) := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton i).subset ?_
    intro j hj
    simp only [Set.mem_singleton_iff]
    by_contra heq
    exact hj ((abs_le.mp (hbound i j (Ne.symm heq))).2)
  have hbound_neg : ∀ᶠ (j : Fin d → ℤ) in Filter.cofinite,
      -(C * Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ)))
        ≤ truncated2Infinite (IsingModel.latticeGraph d) Λ p i j := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton i).subset ?_
    intro j hj
    simp only [Set.mem_singleton_iff]
    by_contra heq
    exact hj ((abs_le.mp (hbound i j (Ne.symm heq))).1)
  -- Step 3: squeeze with -g and g (both → 0).
  have hng_zero : Filter.Tendsto
      (fun j : Fin d → ℤ =>
        -(C * Real.exp (-α * (IsingModel.latticeDistance d i j : ℝ))))
      Filter.cofinite (nhds 0) := by
    have := hg.neg
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hng_zero hg
    hbound_neg hbound_pos

/-- **Lattice mass / inverse correlation length** for `latticeGraph d`:
the supremum (in `ENNReal`) of nonneg decay rates `α : NNReal` for
which `HasExponentialDecay d Λ p (α : ℝ)` holds. The convention
returns `⊤` (= `+∞`) at trivial slices where every rate works,
and a finite value when the truncated 2-point function admits
some maximal exponential decay rate. -/
noncomputable def latticeMass
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) : ENNReal :=
  sSup ((fun α : NNReal => (α : ENNReal)) ''
    {α : NNReal | HasExponentialDecay d Λ p (α : ℝ)})

/-- **Lattice mass nonneg** (trivial via `bot_le` in `ENNReal`). -/
theorem latticeMass_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) :
    0 ≤ latticeMass d Λ p := bot_le

/-- **Lattice mass lower bound from a validating exponential decay rate**:
if `HasExponentialDecay d Λ p α` holds, then the real rate `α` (viewed in
`ENNReal` via `ofReal`) is bounded above by `latticeMass d Λ p`.

This is the direct bridge from the predicate defining admissible decay rates
to the supremum definition of `latticeMass`; later §17.5 arguments can use it
to turn a uniform exponential-decay estimate into a quantitative mass lower
bound. -/
theorem latticeMass_ge_of_HasExponentialDecay
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ}
    {α : ℝ} (hα : 0 ≤ α) (hdecay : HasExponentialDecay d Λ p α) :
    ENNReal.ofReal α ≤ latticeMass d Λ p := by
  unfold latticeMass
  set αNN : NNReal := ⟨α, hα⟩
  apply le_sSup
  exact ⟨αNN, hdecay, (ENNReal.ofReal_eq_coe_nnreal hα).symm⟩

/-- **Positive lattice mass from a positive validating decay rate**:
if `HasExponentialDecay d Λ p α` holds at some strictly positive real rate,
then `latticeMass d Λ p` is strictly positive.

This is the forward direction complementary to
`HasExponentialDecay_of_latticeMass_pos`, and is the convenient form when a
Simon--Lieb or high-temperature argument has already produced an explicit
uniform exponential-decay rate. -/
theorem latticeMass_pos_of_HasExponentialDecay
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ}
    {α : ℝ} (hα : 0 < α) (hdecay : HasExponentialDecay d Λ p α) :
    0 < latticeMass d Λ p :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hα)
    (latticeMass_ge_of_HasExponentialDecay hα.le hdecay)

/-- **Step 117l bridge, conditional lower-bound form**:
if the concrete pseudo-mass associated to a pair at `h = 0` is known to be
a validating `HasExponentialDecay` rate for `truncated2Infinite`, then its
`ENNReal.ofReal` value is bounded above by `latticeMass`.

This theorem isolates the final algebraic step of the lower-bound side of
GJ §17.5 Lemma 17.5.2 (2nd ed., pp. 311--312). The remaining substantive
work is to prove the uniform-in-exhaustion exponential-decay hypothesis,
typically from a Simon--Lieb / random-current refinement. -/
theorem latticeMass_ge_pseudoMassFromParamsAtPair_of_decay
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    ENNReal.ofReal
        (pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_ge_of_HasExponentialDecay
    (pseudoMassFromParamsAtPair_nonneg hα hr d Λ _ x z) hdecay

/-- **Step 117l bridge, conditional positive-mass form**:
if the concrete pseudo-mass associated to a pair at `h = 0` is positive and
also validates `HasExponentialDecay`, then `latticeMass` is positive.

This is the positivity-oriented companion to
`latticeMass_ge_pseudoMassFromParamsAtPair_of_decay`, intended for later
high-temperature / Simon--Lieb arguments where the pseudo-mass rate is
first shown to be strictly positive and then shown to control `U_2`. -/
theorem latticeMass_pos_of_pseudoMassFromParamsAtPair_decay
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    {Λ : Ambient.Exhaustion (Fin d → ℤ)}
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {J β : ℝ} {x z : Fin d → ℤ}
    (hpos : 0 < pseudoMassFromParamsAtPair hα hr d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hdecay : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      (pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)) :
    0 < latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  latticeMass_pos_of_HasExponentialDecay hpos hdecay

end Ambient
end IsingModel
