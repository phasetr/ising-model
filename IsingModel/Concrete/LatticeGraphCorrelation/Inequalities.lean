import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp

/-!
# Inequalities, §5.1 cluster decay, and §17 lattice mass at ℤ^d

ℤ^d wrappers for:
1. GHS inequality (truncated3 ≤ 0) and Lebowitz inequality (truncated4 ≤ 0)
2. §5.3 Z₂ h-symmetry and abs-h theorems
3. §5.1 conditional and distance-based cluster decay
4. §17.1/§17.5 lattice mass / correlation length
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ## Concrete Lebowitz / GHS inequalities on ℤ^d -/

/-- **GHS `U_3 ≤ 0` on ℤ^d** (Glimm–Jaffe §4.3 Cor 4.3.4): for
ferromagnetic `p` and pairwise distinct `r, s : Fin d → ℤ`
(with both non-zero to ensure distinctness from the anchor `0`),
`truncated3TwoPoint d p r s ≤ 0`.

Direct application of `truncated3Infinite_nonpos` at `i = 0, j = r, k = s`
under the three distinctness hypotheses `0 ≠ r, r ≠ s, 0 ≠ s`. -/
theorem truncated3TwoPoint_nonpos_of_distinct
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {r s : Fin d → ℤ} (hr : (0 : Fin d → ℤ) ≠ r)
    (hrs : r ≠ s) (hs : (0 : Fin d → ℤ) ≠ s) :
    truncated3TwoPoint d p r s ≤ 0 :=
  truncated3Infinite_nonpos (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf hr hrs hs

/-- **Lebowitz `U_4 ≤ 0` on ℤ^d at `h = 0`** (Glimm–Jaffe §4.3 Cor 4.3.3):
for ferromagnetic `⟨J, 0, β⟩` and pairwise distinct `r, s, u : Fin d → ℤ`
(all three non-zero + pairwise distinct),
`truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0`.

Direct application of `truncated4Infinite_nonpos_h_zero` at
`i = 0, j = r, k = s, l = u`. -/
theorem truncated4TwoPoint_nonpos_h_zero_of_distinct
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    truncated4TwoPoint d ⟨J, 0, β⟩ r s u ≤ 0 :=
  truncated4Infinite_nonpos_h_zero (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hf hr hs hu hrs hru hsu

/-! ## ℤ^d wrappers for §5.3 Z₂ h-symmetry abs-h theorems (issue #770 A-6) -/

/-- **ℤ^d `|M_Λ(h)| = M_Λ(|h|)`** under ferromagnetism at `|h|`.
Concrete `latticeGraph d` wrapper for PR #772's
`abs_magnetizationΛ_eq_magnetizationΛ_abs_h`. -/
theorem abs_magnetizationΛ_latticeGraph_eq_magnetizationΛ_latticeGraph_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : ↑Λ) :
    |magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i|
      = magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  abs_magnetizationΛ_eq_magnetizationΛ_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i

/-- **ℤ^d `M_along(-h) n = -M_along(h) n`** (any parameters). Concrete
`latticeGraph d` wrapper for PR #773's
`magnetizationAlongExhaustion_neg_h`. -/
theorem magnetizationAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = -magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d `|M_along(h) n| = M_along(|h|) n`** under ferromagnetism at
`|h|`. Concrete `latticeGraph d` wrapper for PR #773's
`abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h`. -/
theorem abs_magnetizationAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i n|
      = magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
  abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i n

/-- **ℤ^d ∞-volume one-sided `|M_∞(h)| ≤ M_∞(|h|)`** under ferromagnetism
at `|h|`. Concrete `latticeGraph d` wrapper for PR #773's
`abs_magnetizationInfinite_le_magnetizationInfinite_abs_h`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_magnetizationInfinite_latticeGraph_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i|
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  abs_magnetizationInfinite_le_magnetizationInfinite_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i

/-- **ℤ^d `M_∞ ≤ 0` at `h ≤ 0`** under ferromagnetism. Concrete
`latticeGraph d` wrapper for PR #774's
`magnetizationInfinite_nonpos_of_nonpos_h`. -/
theorem magnetizationInfinite_latticeGraph_nonpos_of_nonpos_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 :=
  magnetizationInfinite_nonpos_of_nonpos_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ hh i

/-- **ℤ^d `M_∞ = 0` at `h ≤ 0` when some stage misses `i`**.
Concrete `latticeGraph d` wrapper for PR #774's
`magnetizationInfinite_eq_zero_of_exists_stage_not_mem`. -/
theorem magnetizationInfinite_latticeGraph_eq_zero_of_exists_stage_not_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0)
    (i : Fin d → ℤ) (hmiss : ∃ n, i ∉ Λ.volume n) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationInfinite_eq_zero_of_exists_stage_not_mem
    (IsingModel.latticeGraph d) Λ J h β hJ hβ hh i hmiss

/-! ## ℤ^d wrapper for §5.3 A-4 `susceptibilityΛ_eq_abs_h` (issue #770) -/

/-- **ℤ^d `χ_Λ(|h|) = χ_Λ(h) + M_Λ(|h|) − M_Λ(h)`** (no ferromagnetic
hypothesis). Concrete `latticeGraph d` wrapper for PR #776's
`susceptibilityΛ_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityΛ_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h β : ℝ) (i : ↑Λ) :
    susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i
      = susceptibilityΛ (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i
          + magnetizationΛ (IsingModel.latticeGraph d) Λ
            (⟨J, |h|, β⟩ : IsingParams ℝ) i
          - magnetizationΛ (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i :=
  susceptibilityΛ_eq_abs_h (IsingModel.latticeGraph d) Λ J h β i

/-! ## ℤ^d wrapper for §5.3 A-4b `susceptibilityAlongExhaustion_eq_abs_h`
(issue #770) -/

/-- **ℤ^d along-exhaustion `χ_along(|h|) = χ_along(h) + M_along(|h|) − M_along(h)`**
(no ferromagnetic hypothesis). Concrete `latticeGraph d` wrapper for PR
#777's `susceptibilityAlongExhaustion_eq_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n
      = susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, h, β⟩ : IsingParams ℝ) i n
          + magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, |h|, β⟩ : IsingParams ℝ) i n
          - magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
              (⟨J, h, β⟩ : IsingParams ℝ) i n :=
  susceptibilityAlongExhaustion_eq_abs_h (IsingModel.latticeGraph d) Λ J h β i n

/-! ## ℤ^d wrappers for §5.3 A-4c (pointwise) and A-5′
(∞-volume one-sided under BddAbove) (issue #770) -/

/-- **ℤ^d pointwise `χ_along(h) ≤ χ_along(|h|)`** under `0 ≤ J`, `0 < β`.
Concrete `latticeGraph d` wrapper for PR #778's
`susceptibilityAlongExhaustion_le_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityAlongExhaustion_latticeGraph_le_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i n
      ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
  susceptibilityAlongExhaustion_le_abs_h (IsingModel.latticeGraph d) Λ
    J h β hJ hβ i n

/-- **ℤ^d ∞-volume one-sided `χ_∞(h) ≤ χ_∞(|h|)`** (A-5′) under
`0 ≤ J`, `0 < β`, and `BddAbove` of the `|h|`-side along-exhaustion
sequence. Concrete `latticeGraph d` wrapper for PR #778's
`susceptibilityInfinite_le_abs_h`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.3 pp. 77–80. -/
theorem susceptibilityInfinite_latticeGraph_le_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ)
    (hbd : BddAbove (Set.range fun n =>
      susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, |h|, β⟩ : IsingParams ℝ) i n)) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  susceptibilityInfinite_le_abs_h (IsingModel.latticeGraph d) Λ
    J h β hJ hβ i hbd

/-! ## ℤ^d wrapper for §5.1 conditional cluster decay (PR #779) -/

/-- **ℤ^d conditional cluster decay (cofinite form)**: on ℤ^d, if the
∞-volume Ursell 2-point function at a fixed site `i : Fin d → ℤ`,
viewed as a function of the free site `j : Fin d → ℤ`, is summable,
then it tends to `0` along `Filter.cofinite` (which on `Fin d → ℤ`
coincides with the "|r| → ∞" filter). Concrete `latticeGraph d`
wrapper for PR #779's
`truncated2Infinite_tendsto_cofinite_zero_of_summable`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      Filter.cofinite (nhds 0) :=
  truncated2Infinite_tendsto_cofinite_zero_of_summable
    (IsingModel.latticeGraph d) Λ p i hsum

/-! ## ℤ^d distance-based cluster decay capstone

Combines PR #779's cofinite cluster decay with PR #782's proper-map
property of `latticeDistance` (via the filter equality
`comap_latticeDistance_atTop_eq_cofinite` from PR #783) to express
the §5.1 cluster decay statement in its standard distance-based
form. -/

/-- **ℤ^d distance-based conditional cluster decay**: under
summability of `j ↦ U_2(i, j)` at a fixed basepoint
`i : Fin d → ℤ`, the ∞-volume Ursell 2-point function tends to `0`
as the lattice distance `latticeDistance d i j` tends to infinity.

Equivalent ε-N statement: for every `ε > 0` there exists `N : ℕ`
such that `latticeDistance d i j ≥ N` implies
`|truncated2Infinite (latticeGraph d) Λ p i j| < ε`.

A `Summable`-conditioned corollary, not a standalone Glimm–Jaffe
result: it presents the §5.1 cluster picture in its distance-based
form, with the `Summable` hypothesis serving as a placeholder for
the unconditional summability that the Simon–Lieb inequality
(Friedli–Velenik Prop 9.31) is expected to provide in subsequent
PRs. Capstone of the §5.1 cluster-decay infrastructure stack
(PR #779 + PR #781 + PR #782). The proof is a one-line rewrite of
the comap filter via `comap_latticeDistance_atTop_eq_cofinite`,
followed by PR #779's cofinite version.

References: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1
pp. 76–79; Friedli–Velenik *Statistical Mechanics of Lattice
Systems*, Prop 9.31 (Simon–Lieb inequality). -/
theorem truncated2Infinite_latticeGraph_tendsto_atTop_zero_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i : Fin d → ℤ)
    (hsum : Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    Filter.Tendsto
      (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)
      (Filter.comap (fun j : Fin d → ℤ =>
        IsingModel.latticeDistance d i j) Filter.atTop) (nhds 0) := by
  rw [IsingModel.comap_latticeDistance_atTop_eq_cofinite]
  exact truncated2Infinite_latticeGraph_tendsto_cofinite_zero_of_summable
    d Λ p i hsum

/-! ## ℤ^d wrappers for §5.1 cluster property (PR #792 bundle) -/

/-- **ℤ^d cluster property from per-site summability** (Glimm–Jaffe
§5.1): on `latticeGraph d`, if the ∞-volume Ursell 2-point function
`j ↦ U_2(i, j)` is `Summable` for every basepoint `i : Fin d → ℤ`,
then the cluster property holds. Concrete `latticeGraph d` wrapper
of the abstract `clusterProperty_of_summable`. -/
theorem clusterProperty_latticeGraph_of_summable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hsum : ∀ i : Fin d → ℤ,
      Summable (fun j : Fin d → ℤ =>
        truncated2Infinite (IsingModel.latticeGraph d) Λ p i j)) :
    clusterProperty (IsingModel.latticeGraph d) Λ p :=
  clusterProperty_of_summable (IsingModel.latticeGraph d) Λ p hsum

/-- **ℤ^d cluster property at `J = 0` trivial slice (ferromagnetic)**:
on `latticeGraph d`, for ferromagnetic `⟨0, h, β⟩` (`0 ≤ h, 0 < β`),
the cluster property holds. Concrete `latticeGraph d` wrapper of
`clusterProperty_J_zero`. -/
theorem clusterProperty_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨0, h, β⟩ : IsingParams ℝ) :=
  clusterProperty_J_zero (IsingModel.latticeGraph d) Λ h β hf

/-- **ℤ^d cluster property at `β = 0` trivial slice**: on
`latticeGraph d`, for any `⟨J, h, 0⟩`, the cluster property holds
(no ferromagnetic hypothesis). Concrete `latticeGraph d` wrapper
of `clusterProperty_beta_zero`. -/
theorem clusterProperty_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) :
    clusterProperty (IsingModel.latticeGraph d) Λ
      (⟨J, h, 0⟩ : IsingParams ℝ) :=
  clusterProperty_beta_zero (IsingModel.latticeGraph d) Λ J h

/-! ## §17.1 / §17.5 lattice mass / correlation length foundation

Bundled foundation for GJ §17.1 (mass m(σ) of (17.1.5)) and
§17.5 (correlation length) on the lattice. Defines the
exponential-decay predicate `HasExponentialDecay`, proves it at
the trivial slices `β = 0` and `J = 0` (ferromagnetic), and
provides α-monotonicity sanity. The link to the cluster-property
predicate of PR #792 is deferred to a follow-up PR (the proof
needs a `Filter.Tendsto.comp` chain or a Summable derivation;
both are substantive).

The general non-trivial-slice exponential decay rate (positive
mass for `β < β_c`) requires the Simon–Lieb inequality or
random-current representation, both research-level (Issue #780).

References:
* Glimm–Jaffe *Quantum Physics* 2nd ed., §17.1 pp. 304–306.
* Friedli–Velenik, §6 (cluster property), Prop 9.31 (Simon–Lieb). -/

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

/-! ## §17.5 latticeMass — formal definition + nonneg sanity

Defines the lattice mass / inverse correlation length
`latticeMass d Λ p : ENNReal` as the supremum of decay rates
`α : NNReal` for which `HasExponentialDecay d Λ p (α : ℝ)` holds,
extended to `ENNReal`. Trivial slices (β = 0, J = 0 ferromagnetic)
give `latticeMass = ⊤` (decay arbitrarily fast since `U_2 ≡ 0`
or `U_2 = 0` off-diagonally), matching the physical picture that
no correlation = infinite mass = zero correlation length.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §17.1 pp. 304–306. -/

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

/-- **Lattice mass at `β = 0` trivial slice is `⊤`**.
At infinite temperature, `HasExponentialDecay` holds at every
rate `α` (by `HasExponentialDecay_beta_zero`). For any candidate
upper bound `b ≠ ⊤` of the supremand, pick the witness
`α := b.toNNReal + 1`; then `(α : ENNReal) = b + 1 > b`, but the
upper-bound hypothesis would force `(α : ENNReal) ≤ b`. -/
theorem latticeMass_top_of_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) :
    latticeMass d Λ (⟨J, h, 0⟩ : IsingParams ℝ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  -- pick α : NNReal with (α : ENNReal) > b: take b.toNNReal + 1.
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay d Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) (α : ℝ)} :=
    ⟨α, HasExponentialDecay_beta_zero d Λ J h (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b :=
    ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  have hlt : b < b + 1 := ENNReal.lt_add_right hb_ne_top one_ne_zero
  exact absurd hα_le_b (not_le.mpr hlt)

/-- **Lattice mass at `J = 0` ferromagnetic trivial slice is `⊤`**.
Same argument as `latticeMass_top_of_beta_zero` using
`HasExponentialDecay_J_zero`. -/
theorem latticeMass_top_of_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    latticeMass d Λ (⟨0, h, β⟩ : IsingParams ℝ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) (α : ℝ)} :=
    ⟨α, HasExponentialDecay_J_zero d Λ h β (α : ℝ) hf, rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b :=
    ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  have hlt : b < b + 1 := ENNReal.lt_add_right hb_ne_top one_ne_zero
  exact absurd hα_le_b (not_le.mpr hlt)

/-! ## §5.1 Step 110: High-temperature exponential decay (Glimm–Jaffe §5.1 pp. 74–75)

Lifts the ∞-volume Simon-Lieb inequality (Step 109) to an explicit
exponential decay rate: for `βJD < 1` (D = 2d), the two-point
correlation decays as `C · (βJD)^dist(i,j)` where `C = 1/(1-βJD)`.

References: Glimm–Jaffe §5.1 pp. 74–75; Friedli–Velenik Prop. 9.31 p. 428. -/

/-- **Inductive bound (Step 110 core)**: at `h = 0`, `0 ≤ βJ`, `βJD < 1`
(D = 2d), for `i ≠ j` with `dist(i,j) ≥ n+1`:
`⟨σ_iσ_j⟩_∞ ≤ (βJD)^n · (βJD/(1-βJD))`.

Proof by induction on `n` (universalized over `i, j` for the IH):
- n = 0: per-stage `⟨σ_iσ_j⟩_n ≤ χ_n(i) ≤ βJD/(1-βJD)` (Step 106).
- n → n+1: `dist ≥ n+2 → ¬Adj` → Simon-Lieb (Step 109) + triangle + IH.

References: Glimm–Jaffe §5.1 pp. 74–75; Friedli–Velenik Prop. 9.31 p. 428. -/
private lemma correlationInfinite_latticeGraph_le_of_dist_ge
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J) (hlt : β * J * ↑(2 * d) < 1)
    {i j : Fin d → ℤ} (hij : i ≠ j)
    (n : ℕ) (hn : n + 1 ≤ IsingModel.latticeDistance d i j) :
    correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ (β * J * ↑(2 * d)) ^ n *
          (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
  -- Universalize over (i, j) so the IH applies to neighbors (k, j)
  suffices h_univ : ∀ (n : ℕ) (i j : Fin d → ℤ), i ≠ j →
      n + 1 ≤ IsingModel.latticeDistance d i j →
      correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
        ≤ (β * J * ↑(2 * d)) ^ n *
            (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) from
    h_univ n i j hij hn
  intro n
  induction n with
  | zero =>
    intro i j hij _
    simp only [pow_zero, one_mul]
    rw [correlationInfinite_eq_ciSup]
    apply ciSup_le
    intro n'
    by_cases hA : ({i, j} : Finset _) ⊆ (Ambient.cubicExhaustion d).volume n'
    · have hi : i ∈ (Ambient.cubicExhaustion d).volume n' :=
        hA (Finset.mem_insert_self i {j})
      have hj : j ∈ (Ambient.cubicExhaustion d).volume n' :=
        hA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j)))
      rw [correlationAlongExhaustion_of_subset _ _ _ hA, correlationΛ_apply]
      have h_lift : liftFinset ({i, j} : Finset _) hA =
          ({⟨i, hi⟩, ⟨j, hj⟩} : Finset ↑((Ambient.cubicExhaustion d).volume n')) := by
        ext ⟨x, _⟩; simp [mem_liftFinset, Subtype.ext_iff]
      rw [h_lift]
      set G' := inducedGraph (IsingModel.latticeGraph d) ((Ambient.cubicExhaustion d).volume n')
      -- Nonnegativity of truncated2 from hβJ via random-current representation
      have hWpos : 0 < Current.weightSum (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n') ∅ β J := by
        have hZ := IsingModel.partitionFunction_pos G' (⟨J, 0, β⟩ : IsingParams ℝ)
        rw [partitionFunction_inducedGraph_eq_pow_card_mul_weightSum_empty
            (IsingModel.latticeGraph d) _ hβJ] at hZ
        have h2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ↑((Ambient.cubicExhaustion d).volume n') :=
          by positivity
        exact (mul_pos_iff.mp hZ).elim (·.2) (fun h => absurd h2 (not_lt.mpr h.1.le))
      have h_trunc_nn : ∀ k : ↑((Ambient.cubicExhaustion d).volume n'),
          0 ≤ truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ k := fun k => by
        classical
        rw [truncated2_h_zero, correlation_inducedGraph_eq_weightSum_ratio _ _ hβJ]
        exact div_nonneg (Current.weightSum_nonneg _ _ _ hβJ) hWpos.le
      -- corr{⟨i,hi⟩,⟨j,hj⟩} ≤ ∑_k trunc2(⟨i,hi⟩,k) = suscept ≤ βJD/(1-βJD)
      calc IsingModel.correlation G' (⟨J, 0, β⟩ : IsingParams ℝ) {⟨i, hi⟩, ⟨j, hj⟩}
            = truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ ⟨j, hj⟩ :=
              (truncated2_h_zero G' J β ⟨i, hi⟩ ⟨j, hj⟩).symm
          _ ≤ ∑ k : ↑((Ambient.cubicExhaustion d).volume n'),
                truncated2 G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ k :=
              Finset.single_le_sum (fun k _ => h_trunc_nn k) (Finset.mem_univ _)
          _ = IsingModel.susceptibility G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩ :=
              (susceptibility_apply G' (⟨J, 0, β⟩ : IsingParams ℝ) ⟨i, hi⟩).symm
          _ = susceptibilityAlongExhaustion (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) i n' :=
              (susceptibilityAlongExhaustion_of_mem (IsingModel.latticeGraph d)
                (Ambient.cubicExhaustion d) _ hi).symm
          _ ≤ β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d)) :=
              susceptibilityAlongExhaustion_latticeGraph_le_of_high_temp hβJ hlt i n'
    · rw [correlationAlongExhaustion_of_not_subset _ _ _ hA]
      exact div_nonneg (mul_nonneg hβJ (Nat.cast_nonneg _)) (by linarith)
  | succ n ih =>
    -- ih : ∀ i j, i ≠ j → n + 1 ≤ dist d i j → corr{i,j} ≤ (βJD)^n * bound
    intro i j hij hn
    -- dist(i,j) ≥ n+2 ≥ 2 → ¬Adj i j
    have hnadj : ¬(IsingModel.latticeGraph d).Adj i j := by
      rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]; omega
    -- Apply Simon-Lieb (Step 109)
    apply (correlationInfinite_simon_lieb_latticeGraph hβJ hij hnadj).trans
    -- Bound each neighbor term via IH, then sum ≤ D · bound
    have h_each : ∀ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {k, j}
          ≤ (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
      intro k hk
      have hk_adj := (SimpleGraph.mem_neighborFinset _ _ _).mp hk
      have hik_dist : IsingModel.latticeDistance d i k = 1 :=
        (IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one d i k).mp hk_adj
      have h_tri : n + 1 ≤ IsingModel.latticeDistance d k j := by
        have htri := IsingModel.latticeDistance_triangle d i k j
        rw [hik_dist] at htri; omega
      have hkj : k ≠ j := by
        intro heq; rw [heq, IsingModel.latticeDistance_self] at h_tri; omega
      exact ih k j hkj h_tri
    have hdeg : ((IsingModel.latticeGraph d).neighborFinset i).card ≤ 2 * d := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact latticeGraph_degree_le d i
    have h_pow_nn := pow_nonneg (mul_nonneg hβJ (Nat.cast_nonneg (2 * d))) n
    have h_bound_nn := div_nonneg (mul_nonneg hβJ (Nat.cast_nonneg (2 * d)))
        (by linarith : (0 : ℝ) ≤ 1 - β * J * ↑(2 * d))
    calc β * J * ∑ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
              correlationInfinite _ _ _ {k, j}
        ≤ β * J * ∑ k ∈ (IsingModel.latticeGraph d).neighborFinset i,
              (β * J * ↑(2 * d)) ^ n *
                (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_each) hβJ
      _ = β * J * ((IsingModel.latticeGraph d).neighborFinset i).card *
              (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ β * J * ↑(2 * d) * (β * J * ↑(2 * d)) ^ n *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg) hβJ) h_pow_nn)
              h_bound_nn
      _ = (β * J * ↑(2 * d)) ^ (n + 1) *
              (β * J * ↑(2 * d) / (1 - β * J * ↑(2 * d))) := by rw [pow_succ]; ring

open IsingModel in
/-- **High-temperature exponential decay** (Glimm–Jaffe §5.1 pp. 74–75;
Friedli–Velenik Prop. 9.31 p. 428): for the `d`-dimensional lattice graph
with cubic exhaustion, `0 ≤ βJ`, and `βJD < 1` (D = 2d),
`HasExponentialDecay d (cubicExhaustion d) ⟨J,0,β⟩ (-log(βJD))`.

Witness constant `C = 1/(1-βJD)`. The inductive lemma
`correlationInfinite_latticeGraph_le_of_dist_ge` gives
`⟨σ_iσ_j⟩_∞ ≤ C · (βJD)^dist(i,j)`,
and `(βJD)^n ≤ exp(log(βJD) · n) = exp(-(-log βJD) · n)` closes the bound.

**Edge case**: when `βJD = 0` (i.e., `J = 0` or `β = 0`), Lean's convention
`Real.log 0 = 0` gives rate `0` (trivial bound `C · 1`) rather than the
textbook's physically-infinite mass.  The statement remains valid (the bound
`|⟨σ_iσ_j⟩_∞| ≤ C` follows from the inductive lemma at `βJD = 0`),
and the physically meaningful regime is `0 < βJD < 1`.

References: Glimm–Jaffe §5.1 pp. 74–75; Friedli–Velenik Prop. 9.31 p. 428. -/
theorem hasExponentialDecay_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
        (-Real.log (β * J * ↑(2 * d))) := by
  set βJD := β * J * ↑(2 * d) with hβJD_def
  have hβJDnn : 0 ≤ βJD := mul_nonneg hβJ (Nat.cast_nonneg _)
  refine ⟨1 / (1 - βJD), div_nonneg zero_le_one (by linarith), fun i j hij => ?_⟩
  rw [truncated2Infinite_h_zero (latticeGraph d) (cubicExhaustion d) J β i j]
  rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (latticeGraph d)
      (cubicExhaustion d) hβJ {i, j})]
  set N := latticeDistance d i j
  have hN_pos : 0 < N := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hij ((latticeDistance_eq_zero_iff d i j).mp h)
  have h_ind : correlationInfinite (latticeGraph d) (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ βJD ^ (N - 1) * (βJD / (1 - βJD)) :=
    correlationInfinite_latticeGraph_le_of_dist_ge hβJ hlt hij (N - 1) (by omega)
  have h_C_pow : βJD ^ (N - 1) * (βJD / (1 - βJD)) = 1 / (1 - βJD) * βJD ^ N := by
    rw [← mul_div_assoc, ← pow_succ, Nat.sub_add_cancel hN_pos]; ring
  -- (βJD)^N ≤ exp(log βJD * N) = exp(-(-log βJD) * N)
  have h_pow_le_exp : βJD ^ N ≤ Real.exp (Real.log βJD * ↑N) := by
    by_cases hβJD0 : βJD = 0
    · simp [hβJD0, zero_pow hN_pos.ne', Real.log_zero]
    · have hpos : 0 < βJD := lt_of_le_of_ne hβJDnn (Ne.symm hβJD0)
      rw [mul_comm, ← Real.log_pow, Real.exp_log (pow_pos hpos N)]
  calc correlationInfinite (latticeGraph d) (cubicExhaustion d) _ {i, j}
      ≤ βJD ^ (N - 1) * (βJD / (1 - βJD)) := h_ind
    _ = 1 / (1 - βJD) * βJD ^ N := h_C_pow
    _ ≤ 1 / (1 - βJD) * Real.exp (Real.log βJD * ↑N) :=
          mul_le_mul_of_nonneg_left h_pow_le_exp (div_nonneg zero_le_one (by linarith))
    _ = 1 / (1 - βJD) * Real.exp (-(-Real.log βJD) * ↑N) := by simp [neg_neg]

/-! ## §17.5 Step 111: Positive lattice mass at high temperature -/

open IsingModel in
/-- **Positive lattice mass at high temperature** (GJ §17.5 pp. 304–306):
for `0 < βJ` and `βJD < 1` (D = 2d), the lattice mass is positive,
i.e., the correlation length is finite.

For `d = 0`: `Fin 0 → ℤ` is a singleton, `HasExponentialDecay` holds
vacuously for any rate; `latticeMass ≥ 1 > 0`.
For `d ≥ 1`: `hasExponentialDecay_of_high_temp` (Step 110) gives rate
`α₀ = -log(βJD) > 0` (since `0 < βJD < 1`); `latticeMass ≥ α₀ > 0`.

Reference: Glimm–Jaffe §17.5 pp. 304–306. -/
theorem latticeMass_pos_of_high_temp
    {d : ℕ} {β J : ℝ} (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: Fin 0 → ℤ is a singleton, all pairs i ≠ j are vacuous
    have h_vac : HasExponentialDecay 0 (cubicExhaustion 0)
        (⟨J, 0, β⟩ : IsingParams ℝ) (1 : ℝ) :=
      ⟨0, le_refl _, fun i j hij =>
        absurd (funext (fun x => Fin.elim0 x)) hij⟩
    exact lt_of_lt_of_le (by norm_num)
      (le_sSup (show ((1 : NNReal) : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
          {α : NNReal | HasExponentialDecay 0 (cubicExhaustion 0)
              (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ)} from ⟨1, h_vac, rfl⟩))
  · -- d ≥ 1: α₀ = -log(βJD) > 0
    have hβJD_pos : 0 < β * J * ↑(2 * d) :=
      mul_pos hβJ (Nat.cast_pos.mpr (by omega))
    have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
      neg_pos.mpr (Real.log_neg hβJD_pos hlt)
    set α₀ : NNReal := ⟨-Real.log (β * J * ↑(2 * d)), le_of_lt hα_pos⟩
    have h_mem : (α₀ : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
        {α : NNReal | HasExponentialDecay d (cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ)} :=
      ⟨α₀, hasExponentialDecay_of_high_temp hβJ.le hlt, rfl⟩
    apply lt_of_lt_of_le _ (le_sSup h_mem)
    have : (0 : ℝ) < (α₀ : ℝ) := hα_pos
    exact_mod_cast this

end Ambient

end IsingModel
