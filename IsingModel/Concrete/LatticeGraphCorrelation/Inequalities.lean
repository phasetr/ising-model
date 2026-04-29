import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.AmbientFKG
import IsingModel.Inequalities.HighTemp
import IsingModel.LatticeExpSum
import IsingModel.BetaDerivative

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

/-- **GJ §17.3 (17.3.1) lower bound on U₄^∞ on ℤ^d** (Glimm–Jaffe §17.3 p. 308 eq. (17.3.1)):
for ferromagnetic `⟨J, 0, β⟩` and pairwise distinct `r, s, u : Fin d → ℤ`,
`-(corr{0,s}·corr{r,u} + corr{0,u}·corr{r,s}) ≤ truncated4TwoPoint d ⟨J,0,β⟩ r s u`.

Direct application of `truncated4Infinite_ge_neg_pair_correlations` at `i=0, j=r, k=s, l=u`. -/
theorem truncated4TwoPoint_ge_neg_pair_correlations_of_distinct
    (d : ℕ) (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {r s u : Fin d → ℤ}
    (hr : (0 : Fin d → ℤ) ≠ r) (hs : (0 : Fin d → ℤ) ≠ s)
    (hu : (0 : Fin d → ℤ) ≠ u)
    (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    -(correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {0, s} *
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {r, u} +
      correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {0, u} *
        correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
          ⟨J, 0, β⟩ {r, s})
    ≤ truncated4TwoPoint d ⟨J, 0, β⟩ r s u :=
  truncated4Infinite_ge_neg_pair_correlations (IsingModel.latticeGraph d)
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

/-- **Lattice mass is independent of exhaustion** for ferromagnetic parameters:
`latticeMass d Λ p = latticeMass d Λ' p` for any two exhaustions `Λ, Λ'` when `p` is
ferromagnetic.

Proof: `truncated2Infinite_indep_exhaustion` gives `truncated2Infinite G Λ p i j =
truncated2Infinite G Λ' p i j` for all `i, j`. Hence `HasExponentialDecay d Λ p α ↔
HasExponentialDecay d Λ' p α`, so the defining supremand sets are equal and the sSup
values agree.

**Consequence**: for ferromagnetic `p` (i.e. `J ≥ 0`, `β > 0`), the value of
`latticeMass` — and hence the set of valid exponential decay rates — does not depend
on the choice of exhaustion. This relies on `correlationInfinite_indep_exhaustion`
(which itself requires `Ferromagnetic p`). -/
theorem latticeMass_indep_exhaustion
    {d : ℕ} (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) :
    latticeMass d Λ p = latticeMass d Λ' p := by
  unfold latticeMass
  have h_sets : {α : NNReal | HasExponentialDecay d Λ p (α : ℝ)} =
                {α : NNReal | HasExponentialDecay d Λ' p (α : ℝ)} := by
    ext α
    constructor
    · rintro ⟨C, hC, hbound⟩
      exact ⟨C, hC, fun i j hij => by
        rw [← truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j]
        exact hbound i j hij⟩
    · rintro ⟨C, hC, hbound⟩
      exact ⟨C, hC, fun i j hij => by
        rw [truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j]
        exact hbound i j hij⟩
  rw [h_sets]

/-- **Lattice mass via `cubicExhaustion`** equals lattice mass via any exhaustion
for ferromagnetic parameters. Corollary of `latticeMass_indep_exhaustion`. -/
theorem latticeMass_indep_cubicExhaustion
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) :
    latticeMass d Λ p = latticeMass d (Ambient.cubicExhaustion d) p :=
  latticeMass_indep_exhaustion Λ (Ambient.cubicExhaustion d) hf

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

/-- **Lattice mass lower bound in high-temperature regime** (Step 152, GJ §17.5):
for `d ≥ 1`, `0 < βJ`, and `βJ·2d < 1`:
`ENNReal.ofReal (-log(βJ·2d)) ≤ latticeMass d (cubicExhaustion d) ⟨J,0,β⟩`.

The rate `α₀ = -log(βJD)` (with `D = 2d`) from Step 110 is in the defining set of
`latticeMass`, so `latticeMass ≥ α₀`. This makes the lower bound from `latticeMass_pos_of_high_temp`
(Step 111) explicit: the exponential decay rate `α₀` is a concrete lower bound for the mass.

Reference: Glimm–Jaffe §17.5 pp. 304–306. -/
theorem latticeMass_ge_neg_log_of_high_temp
    {d : ℕ} (hd : 1 ≤ d) {β J : ℝ} (hβJ : 0 < β * J)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  have hβJD_pos : 0 < β * J * ↑(2 * d) :=
    mul_pos hβJ (Nat.cast_pos.mpr (by omega))
  have hα_pos : 0 < -Real.log (β * J * ↑(2 * d)) :=
    neg_pos.mpr (Real.log_neg hβJD_pos hlt)
  set α₀ : NNReal := ⟨-Real.log (β * J * ↑(2 * d)), le_of_lt hα_pos⟩
  apply le_sSup
  exact ⟨α₀, hasExponentialDecay_of_high_temp hβJ.le hlt,
         (ENNReal.ofReal_eq_coe_nnreal hα_pos.le).symm⟩

/-! ## §17.5 Step 112: Lattice mass antitonicity in β and J -/

/-- **Lattice mass antitone in β** at h = 0 (GJ §17.5 pp. 304–306):
for fixed `J ≥ 0` and `0 < β₁ ≤ β₂`, the lattice mass satisfies
`latticeMass(β₂) ≤ latticeMass(β₁)`.

Physics: higher temperature (lower β) → stronger high-temp regime
→ faster exponential decay → larger mass (shorter correlation length).

Proof: `HasExponentialDecay(β₂, α)` with witness `C` implies the same
for `β₁` using `truncated2Infinite_h_zero` + GKS-II β-monotonicity
(`correlationInfinite_monotone_beta`, GJ Prop 4.2.4) + GKS-I nonnegativity
(`correlationInfinite_nonneg_of_hβJ`).

Reference: Glimm–Jaffe §17.5 pp. 304–306; §4.2 Prop 4.2.4 (β-monotonicity). -/
theorem latticeMass_antitone_beta
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J)
    {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) :
    latticeMass d Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) ≤
    latticeMass d Λ (⟨J, 0, β₁⟩ : IsingParams ℝ) := by
  unfold latticeMass
  apply sSup_le_sSup
  intro a ha
  obtain ⟨α, hα_decay, rfl⟩ := ha
  obtain ⟨C, hC, hbound⟩ := hα_decay
  refine ⟨α, ⟨C, hC, fun i j hij => ?_⟩, rfl⟩
  simp only [truncated2Infinite_h_zero] at hbound ⊢
  have hnn₁ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β₁⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ₁.le hJ) {i, j}
  have hnn₂ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J, 0, β₂⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg (hβ₁.le.trans hβ₁₂) hJ) {i, j}
  rw [abs_of_nonneg hnn₁]
  calc correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₁⟩ : IsingParams ℝ) {i, j}
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β₂⟩ : IsingParams ℝ) {i, j} :=
        correlationInfinite_monotone_beta (IsingModel.latticeGraph d) Λ hJ (le_refl 0) {i, j}
          (Set.mem_Ioi.mpr hβ₁) (Set.mem_Ioi.mpr (hβ₁.trans_le hβ₁₂)) hβ₁₂
      _ ≤ C * Real.exp (-↑α * (IsingModel.latticeDistance d i j : ℝ)) := by
          have hb := hbound i j hij
          rwa [abs_of_nonneg hnn₂] at hb

/-- **Lattice mass antitone in J** at h = 0 (GJ §17.5 pp. 304–306):
for fixed `β > 0` and `0 ≤ J₁ ≤ J₂`, the lattice mass satisfies
`latticeMass(J₂) ≤ latticeMass(J₁)`.

Same argument as `latticeMass_antitone_beta` using GKS-II J-monotonicity
(`correlationInfinite_monotone_J`, GJ Prop 4.2.3) instead.

Reference: Glimm–Jaffe §17.5 pp. 304–306; §4.2 Prop 4.2.3 (J-monotonicity). -/
theorem latticeMass_antitone_J
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂)
    {β : ℝ} (hβ : 0 < β) :
    latticeMass d Λ (⟨J₂, 0, β⟩ : IsingParams ℝ) ≤
    latticeMass d Λ (⟨J₁, 0, β⟩ : IsingParams ℝ) := by
  unfold latticeMass
  apply sSup_le_sSup
  intro a ha
  obtain ⟨α, hα_decay, rfl⟩ := ha
  obtain ⟨C, hC, hbound⟩ := hα_decay
  refine ⟨α, ⟨C, hC, fun i j hij => ?_⟩, rfl⟩
  simp only [truncated2Infinite_h_zero] at hbound ⊢
  have hnn₁ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J₁, 0, β⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ.le hJ₁) {i, j}
  have hnn₂ : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ
      (⟨J₂, 0, β⟩ : IsingParams ℝ) {i, j} :=
    correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d) Λ
      (mul_nonneg hβ.le (hJ₁.trans hJ₁₂)) {i, j}
  rw [abs_of_nonneg hnn₁]
  calc correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₁, 0, β⟩ : IsingParams ℝ) {i, j}
      ≤ correlationInfinite (IsingModel.latticeGraph d) Λ (⟨J₂, 0, β⟩ : IsingParams ℝ) {i, j} :=
        correlationInfinite_monotone_J (IsingModel.latticeGraph d) Λ (le_refl 0) hβ {i, j}
          (Set.mem_Ici.mpr hJ₁) (Set.mem_Ici.mpr (hJ₁.trans hJ₁₂)) hJ₁₂
      _ ≤ C * Real.exp (-↑α * (IsingModel.latticeDistance d i j : ℝ)) := by
          have hb := hbound i j hij
          rwa [abs_of_nonneg hnn₂] at hb

/-! ## §17.5 J-lower bound on the two-point function (Step 113) -/

/-- Spin sign of a product: `sign(a.mul b) = sign(a) * sign(b)` over ℝ. -/
private lemma Spin.sign_mul_ℝ (a b : Spin) :
    Spin.sign ℝ (a.mul b) = Spin.sign ℝ a * Spin.sign ℝ b := by
  simp [Spin.sign, Spin.toSign_mul, Int.cast_mul]

/-- Sum over all `Config ι` of `f(σ i)` equals `(∑ a, f a) * 2 ^ (Fintype.card ι - 1)`.

Proof: express `f(σ i) = ∏_k (if k = i then f(σ k) else 1)` via
`Finset.prod_ite_eq'`, then apply `Finset.sum_prod_piFinset` to
interchange the Config-sum with a product over sites.  The `i`-th
factor yields `∑ a, f a`; each `k ≠ i` factor yields `∑ a : Spin, 1 = 2`. -/
private lemma sum_config_apply_eq_mul_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : Spin → ℝ) :
    ∑ σ : Config ι, f (σ i) = (∑ a : Spin, f a) * 2 ^ (Fintype.card ι - 1) := by
  have hprod : ∀ σ : Config ι, f (σ i) = ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ)) := by
    intro σ
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hprod]
  rw [show ∑ σ : Config ι, ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ))
      = ∑ σ ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Spin)),
          ∏ k : ι, (if k = i then f (σ k) else (1 : ℝ)) from by
        rw [Fintype.piFinset_univ]]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset Spin)
      (fun k a => if k = i then f a else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · rw [show ∏ k ∈ (Finset.univ : Finset ι).erase i,
            ∑ a ∈ (Finset.univ : Finset Spin), (if k = i then f a else (1 : ℝ))
        = ∏ _ ∈ (Finset.univ : Finset ι).erase i, (2 : ℝ) from
      Finset.prod_congr rfl fun k hk => by
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        simp only [if_neg hki, Finset.sum_const, Finset.card_univ, card_spin,
                   Nat.smul_one_eq_cast, Nat.cast_ofNat]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

/-- **Single-edge correlation at `h = 0`**: for a graph `G` with exactly one edge `{i, j}`
and external field `h = 0`, the two-point correlation equals `tanh(β J)`.

Proof: the bijection `φ(σ)(i) = σ i · σ j`, `φ(σ)(j) = σ i` transforms the edge
coupling `J · σ_i · σ_j` into a site field `J · σ_i`, so after the change of variables
both the numerator `∑ sign(σ i) exp(βJ sign(σ i))` and the denominator `∑ exp(βJ sign(σ i))`
factor via `sum_config_apply_eq_mul_pow`; the common `2^(|ι|−1)` cancels, yielding `tanh`. -/
private lemma correlation_singleEdge_h_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {i j : ι} (hij : i ≠ j)
    (hG : G.edgeFinset = ({Sym2.mk i j} : Finset (Sym2 ι)))
    (J β : ℝ) :
    IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {i, j}
      = Real.tanh (β * J) := by
  -- Bijection φ: (σ i, σ j, rest) ↦ (σ i · σ j, σ i, rest)
  let φ_fun : Config ι → Config ι := fun σ x =>
    if x = i then (σ i).mul (σ j) else if x = j then σ i else σ x
  let φ_inv : Config ι → Config ι := fun τ x =>
    if x = i then τ j else if x = j then (τ j).mul (τ i) else τ x
  have hφ_linv : Function.LeftInverse φ_inv φ_fun := fun σ => by
    ext x
    by_cases h1 : x = i
    · subst h1; simp [φ_fun, φ_inv, Ne.symm hij]
    · by_cases h2 : x = j
      · subst h2; simp [φ_fun, φ_inv, h1, Spin.mul_mul_cancel]
      · simp [φ_fun, φ_inv, h1, h2]
  have hφ_rinv : Function.RightInverse φ_inv φ_fun := fun τ => by
    ext x
    by_cases h1 : x = i
    · subst h1; simp [φ_fun, φ_inv, Ne.symm hij, Spin.mul_mul_cancel]
    · by_cases h2 : x = j
      · subst h2; simp [φ_fun, φ_inv, h1]
      · simp [φ_fun, φ_inv, h1, h2]
  let φ : Config ι ≃ Config ι := ⟨φ_fun, φ_inv, hφ_linv, hφ_rinv⟩
  -- Hamiltonian: H(σ) = -J · sign(σ i) · sign(σ j) when edgeFinset = {Sym2.mk i j}
  have hH : ∀ σ : Config ι,
      hamiltonian G (⟨J, 0, β⟩ : IsingParams ℝ) σ
        = -J * (Spin.sign ℝ (σ i) * Spin.sign ℝ (σ j)) := by
    intro σ
    unfold hamiltonian interactionEnergy externalFieldEnergy
    simp only [neg_zero]
    rw [hG, Finset.sum_singleton]
    simp [edgeSpin, Sym2.lift_mk]
  -- Boltzmann weight after φ_inv: exp(β J sign(τ i))
  have hbw : ∀ τ : Config ι,
      boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) (φ_inv τ)
        = Real.exp (β * J * Spin.sign ℝ (τ i)) := fun τ => by
    unfold boltzmannWeight
    rw [hH (φ_inv τ)]
    have hi : φ_inv τ i = τ j := by simp [φ_inv]
    have hj : φ_inv τ j = (τ j).mul (τ i) := by simp [φ_inv, Ne.symm hij]
    rw [hi, hj]
    have key : Spin.sign ℝ (τ j) * Spin.sign ℝ ((τ j).mul (τ i)) = Spin.sign ℝ (τ i) := by
      rw [← Spin.sign_mul_ℝ, Spin.mul_mul_cancel]
    simp only [key]; congr 1; ring
  -- spinProduct {i,j} after φ_inv: sign(τ i)
  have hsp : ∀ τ : Config ι,
      spinProduct ({i, j} : Finset ι) (φ_inv τ) = Spin.sign ℝ (τ i) := fun τ => by
    unfold spinProduct
    rw [Finset.prod_pair hij]
    have hi : φ_inv τ i = τ j := by simp [φ_inv]
    have hj : φ_inv τ j = (τ j).mul (τ i) := by simp [φ_inv, Ne.symm hij]
    rw [hi, hj]
    change Spin.sign ℝ (τ j) * Spin.sign ℝ ((τ j).mul (τ i)) = Spin.sign ℝ (τ i)
    rw [← Spin.sign_mul_ℝ, Spin.mul_mul_cancel]
  -- Partition function via bijection + factorization
  have hZ : ∑ σ : Config ι, boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      (∑ a : Spin, Real.exp (β * J * Spin.sign ℝ a)) * 2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.sum_equiv φ (fun σ => boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ)
        (fun τ => Real.exp (β * J * Spin.sign ℝ (τ i)))
        (fun σ => by
          have h := hbw (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at h; exact h)]
    exact sum_config_apply_eq_mul_pow i (fun a => Real.exp (β * J * Spin.sign ℝ a))
  -- Numerator via bijection + factorization
  have hN : ∑ σ : Config ι, spinProduct ({i, j} : Finset ι) σ *
      boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ =
      (∑ a : Spin, Spin.sign ℝ a * Real.exp (β * J * Spin.sign ℝ a)) *
        2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.sum_equiv φ
        (fun σ => spinProduct ({i, j} : Finset ι) σ *
            boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ)
        (fun τ => Spin.sign ℝ (τ i) * Real.exp (β * J * Spin.sign ℝ (τ i)))
        (fun σ => by
          have hs := hsp (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at hs
          have hb := hbw (φ σ)
          rw [show φ_inv (φ σ) = σ from hφ_linv σ] at hb
          simp only []
          rw [hs, hb])]
    exact sum_config_apply_eq_mul_pow i
      (fun a => Spin.sign ℝ a * Real.exp (β * J * Spin.sign ℝ a))
  -- Assemble: correlation = N / Z = tanh(βJ)
  unfold correlation gibbsExpectation partitionFunction
  rw [hZ, hN, sum_exp_spin_sign β J, sum_spin_sign_exp_sign β J]
  have h2pow_ne : (2 : ℝ) ^ (Fintype.card ι - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos (β * J)).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hcosh_ne, h2pow_ne]

/-- The edgeFinset of `inducedGraph (fromEdgeSet {Sym2.mk 0 r}) Λn` is the singleton
`{Sym2.mk ⟨0,h0n⟩ ⟨r,hrn⟩}` whenever `0, r ∈ Λn` and `0 ≠ r`. -/
private lemma inducedSingleEdge_edgeFinset (d : ℕ)
    {r : Fin d → ℤ} (hr_ne : (0 : Fin d → ℤ) ≠ r)
    {Λn : Finset (Fin d → ℤ)} (h0n : (0 : Fin d → ℤ) ∈ Λn) (hrn : r ∈ Λn)
    [Fintype (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).edgeSet] :
    (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).edgeFinset
      = ({Sym2.mk (⟨0, h0n⟩ : ↑Λn) (⟨r, hrn⟩ : ↑Λn)} : Finset (Sym2 ↑Λn)) := by
  have hG_adj : ∀ (u v : ↑Λn),
      (inducedGraph (SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}) Λn).Adj u v
        ↔ (Sym2.mk (u : Fin d → ℤ) v = Sym2.mk 0 r) ∧ (u : Fin d → ℤ) ≠ v := by
    intros u v
    simp only [inducedGraph_apply, SimpleGraph.induce_adj, SimpleGraph.fromEdgeSet_adj,
               Set.mem_singleton_iff]
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
  refine Sym2.ind (fun u v => ?_) e
  rw [SimpleGraph.mem_edgeSet, hG_adj, Sym2.eq_iff]
  constructor
  · -- mp: (↑u=0 ∧ ↑v=r ∨ ↑u=r ∧ ↑v=0) ∧ ↑u≠↑v → s(u,v) = s(⟨0⟩,⟨r⟩)
    intro ⟨hmem, _⟩
    rw [Sym2.eq_iff]
    rcases hmem with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨Subtype.ext hu, Subtype.ext hv⟩
    · exact Or.inr ⟨Subtype.ext hu, Subtype.ext hv⟩
  · -- mpr: s(u,v) = s(⟨0⟩,⟨r⟩) → (↑u=0 ∧ ↑v=r ∨ ↑u=r ∧ ↑v=0) ∧ ↑u≠↑v
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have h1 : (↑u : Fin d → ℤ) = 0 := congr_arg Subtype.val hu
      have h2 : (↑v : Fin d → ℤ) = r := congr_arg Subtype.val hv
      exact ⟨Or.inl ⟨h1, h2⟩, fun heq => hr_ne (h1 ▸ h2 ▸ heq)⟩
    · have h1 : (↑u : Fin d → ℤ) = r := congr_arg Subtype.val hu
      have h2 : (↑v : Fin d → ℤ) = 0 := congr_arg Subtype.val hv
      exact ⟨Or.inr ⟨h1, h2⟩, fun heq => hr_ne.symm (h2 ▸ h1 ▸ heq)⟩

/-- **J-lower bound on the two-point function** (GJ §17.5 pp. 304–306):
for adjacent `r` in `latticeGraph d`, ferromagnetic `J ≥ 0`, `β > 0`, `h = 0`:

`tanh(β J) ≤ twoPointFunction d ⟨J, 0, β⟩ r`.

Proof: (1) the single-edge graph `G_single = fromEdgeSet {⟦(0,r)⟧}` satisfies
`G_single ≤ latticeGraph d`; (2) `correlationInfinite G_single = tanh(βJ)` by the
single-edge 2-site computation; (3) apply GKS-II subgraph monotonicity.

Reference: Glimm–Jaffe §17.5 pp. 304–306 (2nd ed.); §4.2 (GKS-II subgraph monotonicity). -/
theorem twoPointFunction_ge_tanh_betaJ_of_adj
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : (IsingModel.latticeGraph d).Adj 0 r) :
    Real.tanh (β * J) ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  -- The ferromagnetic condition
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- The single-edge subgraph
  let G_single : SimpleGraph (Fin d → ℤ) :=
    SimpleGraph.fromEdgeSet {Sym2.mk (0 : Fin d → ℤ) r}
  haveI hDecSingle : DecidableRel G_single.Adj := fun u v => by
    simp only [G_single, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
    exact inferInstance
  haveI : ∀ n, Fintype (inducedGraph G_single ((cubicExhaustion d).volume n)).edgeSet :=
    fun n => by
      haveI : DecidableRel (inducedGraph G_single ((cubicExhaustion d).volume n)).Adj :=
        fun ⟨a, _⟩ ⟨b, _⟩ => by unfold inducedGraph SimpleGraph.induce; exact inferInstance
      exact SimpleGraph.fintypeEdgeSet _
  -- G_single ≤ latticeGraph d
  have hG_le : G_single ≤ IsingModel.latticeGraph d := by
    intro u v hadj
    rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hadj
    obtain ⟨hmem, _⟩ := hadj
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact hr.symm
  -- correlationInfinite G_single (cubicExhaustion d) ⟨J,0,β⟩ {0,r} = tanh(βJ)
  have hcorr : correlationInfinite G_single (cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r}
      = Real.tanh (β * J) := by
    -- The sequence is eventually constant at tanh(βJ)
    have h_event : ∀ᶠ n in Filter.atTop,
        correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r} n
          = Real.tanh (β * J) := by
      obtain ⟨N, hN⟩ := (cubicExhaustion d).exhaust {(0 : Fin d → ℤ), r}
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hAn : {(0 : Fin d → ℤ), r} ⊆ (cubicExhaustion d).volume n := hN n hn
      have h0n : (0 : Fin d → ℤ) ∈ (cubicExhaustion d).volume n :=
        hAn (Finset.mem_insert_self 0 {r})
      have hrn : r ∈ (cubicExhaustion d).volume n :=
        hAn (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
      have hr_ne : (0 : Fin d → ℤ) ≠ r := hr.ne
      rw [correlationAlongExhaustion_of_subset G_single (cubicExhaustion d) _ hAn,
          correlationΛ_apply]
      -- Rewrite liftFinset to explicit pair to avoid isDefEq timeout on unification
      have hlift : liftFinset {(0 : Fin d → ℤ), r} hAn =
          ({⟨0, h0n⟩, ⟨r, hrn⟩} : Finset (↑((cubicExhaustion d).volume n))) := by
        ext u; rw [mem_liftFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      rw [hlift]
      exact correlation_singleEdge_h_zero (inducedGraph G_single ((cubicExhaustion d).volume n))
          (by intro heq; exact hr_ne (congr_arg Subtype.val heq))
          (inducedSingleEdge_edgeFinset d hr_ne h0n hrn) J β
    -- The sequence also tends to correlationInfinite (by ferromagnetic monotonicity)
    have h_tendsto := correlationAlongExhaustion_tendsto_ciSup G_single (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), r}
    have h_tendsto_const : Filter.Tendsto
        (correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r})
        Filter.atTop (nhds (Real.tanh (β * J))) :=
      tendsto_const_nhds.congr' (h_event.mono (fun _ heq => heq.symm))
    have h_unique : (⨆ n, correlationAlongExhaustion G_single (cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) {(0 : Fin d → ℤ), r} n) = Real.tanh (β * J) :=
      tendsto_nhds_unique h_tendsto h_tendsto_const
    simp only [correlationInfinite, h_unique]
  -- Apply subgraph monotonicity
  rw [twoPointFunction_apply, ← hcorr]
  exact correlationInfinite_monotone_ambient_subgraph hG_le (cubicExhaustion d)
    (⟨J, 0, β⟩ : IsingParams ℝ) hf {(0 : Fin d → ℤ), r}

/-! ## §17.5 Path lower bound on the two-point function (Step 114) -/

/-- From `latticeDistance d 0 r = n + 1`, find a lattice neighbor of `r` that
is one step closer to `0`.

Proof: since the ℓ¹ sum is n + 1 ≥ 1, some coordinate `i₀` has `|r i₀| ≥ 1`.
Move `r i₀` one step toward 0 to get `v = r[i₀ ↦ r i₀ ∓ 1]`. -/
private lemma exists_latticeDistance_succ_adj
    (d : ℕ) (r : Fin d → ℤ) (n : ℕ)
    (hn : IsingModel.latticeDistance d 0 r = n + 1) :
    ∃ v : Fin d → ℤ, (IsingModel.latticeGraph d).Adj v r ∧
      IsingModel.latticeDistance d 0 v = n := by
  have hsum : ∑ i : Fin d, (r i).natAbs = n + 1 := by
    unfold IsingModel.latticeDistance at hn; simpa [Pi.zero_apply] using hn
  have hne : ∑ i : Fin d, (r i).natAbs ≠ 0 := by omega
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hri₀ : r i₀ ≠ 0 := fun h => by simp [h] at hi₀
  -- erase decomposition
  have h_rest : ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs = n + 1 - (r i₀).natAbs := by
    have h : ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs + (r i₀).natAbs = n + 1 :=
      (Finset.sum_erase_add Finset.univ (fun i => (r i).natAbs) (Finset.mem_univ i₀)).trans hsum
    omega
  -- adjacency: ∑ (update i - r i).natAbs = (x - r i₀).natAbs
  have h_adj_sum : ∀ (x : ℤ),
      ∑ i : Fin d, (Function.update r i₀ x i - r i).natAbs = (x - r i₀).natAbs := by
    intro x
    have heq : ∑ i : Fin d, (Function.update r i₀ x i - r i).natAbs
        = (Function.update r i₀ x i₀ - r i₀).natAbs :=
      Finset.sum_eq_single i₀
        (fun j _ hj => by simp [Function.update_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h)
    simp [heq]
  -- distance: ∑ (0 - update i).natAbs = x.natAbs + ∑ erase
  have h_dist_sum : ∀ (x : ℤ),
      ∑ i : Fin d, (0 - Function.update r i₀ x i).natAbs
        = x.natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
    intro x
    rw [show ∑ i : Fin d, (0 - Function.update r i₀ x i).natAbs
        = ∑ i ∈ insert i₀ (Finset.univ.erase i₀), (0 - Function.update r i₀ x i).natAbs from by
      rw [Finset.insert_erase (Finset.mem_univ i₀)]]
    rw [Finset.sum_insert (Finset.notMem_erase i₀ Finset.univ)]
    simp only [Function.update_apply, zero_sub, Int.natAbs_neg]
    congr 1
    apply Finset.sum_congr rfl; intro j hj
    simp only [if_neg (Finset.mem_erase.mp hj).1]
  -- sum bound: (r i₀).natAbs ≤ n + 1
  have h_bound : (r i₀).natAbs ≤ n + 1 :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)).trans_eq hsum
  rcases lt_or_gt_of_ne hri₀ with h_neg | h_pos
  · -- r i₀ < 0: step v i₀ = r i₀ + 1
    refine ⟨Function.update r i₀ (r i₀ + 1), ?_, ?_⟩
    · rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      unfold IsingModel.latticeDistance; rw [h_adj_sum]; norm_num
    · have : IsingModel.latticeDistance d 0 (Function.update r i₀ (r i₀ + 1))
          = (r i₀ + 1).natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
        unfold IsingModel.latticeDistance; simpa [Pi.zero_apply] using h_dist_sum (r i₀ + 1)
      rw [this, h_rest]; omega
  · -- r i₀ > 0: step v i₀ = r i₀ - 1
    refine ⟨Function.update r i₀ (r i₀ - 1), ?_, ?_⟩
    · rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      unfold IsingModel.latticeDistance; rw [h_adj_sum]; norm_num
    · have : IsingModel.latticeDistance d 0 (Function.update r i₀ (r i₀ - 1))
          = (r i₀ - 1).natAbs + ∑ i ∈ Finset.univ.erase i₀, (r i).natAbs := by
        unfold IsingModel.latticeDistance; simpa [Pi.zero_apply] using h_dist_sum (r i₀ - 1)
      rw [this, h_rest]; omega


/-- **Path lower bound on the two-point function** (GJ §17.5 pp. 304–306):
for any `r ≠ 0` in ℤ^d, ferromagnetic `J ≥ 0`, `β > 0`, `h = 0`:

`tanh(β J)^(latticeDistance d 0 r) ≤ twoPointFunction d ⟨J, 0, β⟩ r`.

Proof: strong induction on `n = latticeDistance d 0 r`.
- Base (`n = 0`): contradicts `r ≠ 0`.
- Step `n + 1`: `exists_latticeDistance_succ_adj` gives `v` with `Adj v r` and `dist 0 v = n`.
  If `n = 0`, then `v = 0` so `Adj 0 r`, and `twoPointFunction_ge_tanh_betaJ_of_adj` applies.
  If `n ≥ 1`, then `v ≠ 0`; apply IH to get `tanh^n ≤ twoPointFunction v`.
  By translation invariance, `correlationInfinite ... {v, r} = twoPointFunction (r−v)`,
  and since `Adj 0 (r−v)`, Step 113 gives `tanh ≤ twoPointFunction (r−v)`.
  GKS-II: `twoPointFunction v * correlationInfinite ... {v, r} ≤ twoPointFunction r`
  (via `{0,v} ∆ {v,r} = {0,r}`), so `tanh^{n+1} ≤ twoPointFunction r`.

Reference: Glimm–Jaffe §17.5 pp. 304–306 (2nd ed.); §4.2 (GKS-II subgraph monotonicity). -/
theorem twoPointFunction_ge_tanh_betaJ_pow_dist
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * J) ^ IsingModel.latticeDistance d 0 r ≤
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hβ.le hJ)) (Real.cosh_pos _).le
  -- Helper: adjacent pair gives tanh lower bound on correlationInfinite
  have h_adj_ge : ∀ (u w : Fin d → ℤ), (IsingModel.latticeGraph d).Adj u w →
      Real.tanh (β * J) ≤ correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {u, w} := by
    intro u w huw
    -- Translate by -u: correlationInfinite {u, w} = correlationInfinite {0, w - u}
    have htrans : correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {u, w}
        = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) (w - u) := by
      rw [twoPointFunction_apply]
      rw [← correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset d (-u)
            (⟨J, 0, β⟩ : IsingParams ℝ) hf]
      congr 1
      unfold vaddFinset
      rw [Finset.image_insert, Finset.image_singleton]
      simp only [vadd_eq_add, neg_add_cancel]
      congr 1; ext i; ring
    -- latticeDistance d 0 (w - u) = latticeDistance d u w = 1
    have h_adj_0 : (IsingModel.latticeGraph d).Adj 0 (w - u) := by
      rw [IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one]
      have huw' : IsingModel.latticeDistance d u w = 1 :=
        (IsingModel.latticeGraph_adj_iff_latticeDistance_eq_one d u w).mp huw
      unfold IsingModel.latticeDistance at huw' ⊢
      simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, Int.natAbs_neg] at huw' ⊢
      calc ∑ i : Fin d, (w i - u i).natAbs
          = ∑ i : Fin d, (u i - w i).natAbs :=
            Finset.sum_congr rfl fun i _ => by
              rw [show (w i - u i : ℤ) = -(u i - w i) from by ring]
              exact Int.natAbs_neg _
        _ = 1 := huw'
    rw [htrans]
    exact twoPointFunction_ge_tanh_betaJ_of_adj hJ hβ h_adj_0
  -- Strong induction on n = latticeDistance d 0 r
  suffices h : ∀ (n : ℕ) (s : Fin d → ℤ),
      IsingModel.latticeDistance d 0 s = n → s ≠ 0 →
      Real.tanh (β * J) ^ n ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s from
    h _ r rfl hr
  intro n
  induction n with
  | zero =>
    intro s h0 hs0
    exact absurd ((IsingModel.latticeDistance_eq_zero_iff d 0 s).mp h0).symm hs0
  | succ n ih =>
    intro s hn hs0
    obtain ⟨v, hv_adj, hv_dist⟩ := exists_latticeDistance_succ_adj d s n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- n = 0: v = 0, Adj 0 s, use Step 113 directly
      have hv0 : v = 0 := ((IsingModel.latticeDistance_eq_zero_iff d 0 v).mp hv_dist).symm
      subst hv0
      simpa using twoPointFunction_ge_tanh_betaJ_of_adj hJ hβ hv_adj
    · -- n ≥ 1: v ≠ 0, use IH + GKS-II
      have hv_ne : v ≠ 0 := by
        intro heq; simp [heq, IsingModel.latticeDistance] at hv_dist; omega
      -- IH
      have ih_v : Real.tanh (β * J) ^ n ≤
          twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v := ih v hv_dist hv_ne
      -- tanh ≤ correlationInfinite {v, s}
      have h_corr_vs : Real.tanh (β * J) ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
        h_adj_ge v s hv_adj
      -- nonnegativity
      have hv_nn : 0 ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v :=
        (pow_nonneg htanh_nn n).trans ih_v
      have hcorr_nn : 0 ≤ correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
        htanh_nn.trans h_corr_vs
      -- Symmetric difference {0, v} ∆ {v, s} = {0, s}
      have h0v : (0 : Fin d → ℤ) ≠ v := Ne.symm hv_ne
      have hvs : v ≠ s := hv_adj.ne
      have h0s : (0 : Fin d → ℤ) ≠ s := Ne.symm hs0
      have hsdiff : ({(0 : Fin d → ℤ), v} : Finset _) ∆ {v, s} = {0, s} := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨rfl | rfl, h2⟩ | ⟨rfl | rfl, h2⟩)
          · exact Or.inl rfl
          · exact absurd (Or.inl rfl) h2
          · exact absurd (Or.inr rfl) h2
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact Or.inl ⟨Or.inl rfl, fun h => h.elim (h0v ·) (h0s ·)⟩
          · exact Or.inr ⟨Or.inr rfl, fun h => h.elim hs0 (fun hv => hvs hv.symm)⟩
      -- GKS-II: twoPointFunction v * correlationInfinite {v, s} ≤ twoPointFunction s
      have hgks : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
          correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, β⟩ : IsingParams ℝ) {v, s}
          ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s :=
        calc twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s}
            = correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {0, v} *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} := by
                  rw [twoPointFunction_apply]
          _ ≤ correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) ({(0 : Fin d → ℤ), v} ∆ {v, s}) :=
                  correlationInfinite_latticeGraph_cubicExhaustion_gks_second d _ hf {0, v} {v, s}
          _ = twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s := by
                  rw [hsdiff, twoPointFunction_apply]
      calc Real.tanh (β * J) ^ (n + 1)
          = Real.tanh (β * J) ^ n * Real.tanh (β * J) := pow_succ _ _
        _ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) v *
              correlationInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) {v, s} :=
              mul_le_mul ih_v h_corr_vs htanh_nn hv_nn
        _ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) s := hgks

/-! ## §17.5 Step 115: Upper bound on the lattice mass -/

/-- For `d ≥ 1` and `n : ℕ`, the axis point `fun i : Fin d => if i.val = 0 then n else 0`
is at `latticeDistance d 0 r = n` from the origin. -/
private lemma latticeDistance_coord_eq {d : ℕ} (hd : 0 < d) (n : ℕ) :
    IsingModel.latticeDistance d 0 (fun i : Fin d => if i.val = 0 then (n : ℤ) else 0) = n := by
  unfold IsingModel.latticeDistance
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
  rw [Finset.sum_eq_single ⟨0, hd⟩
      (fun j _ hj => by simp [show j.val ≠ 0 from fun h => hj (Fin.ext h)])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp

open IsingModel in
/-- **Upper bound on the lattice mass** (GJ §17.5 pp. 304–306):
for `d ≥ 1`, `J > 0`, `β > 0` at `h = 0`,
`latticeMass d (cubicExhaustion d) ⟨J,0,β⟩ ≤ ENNReal.ofReal (-log(tanh(βJ)))`.

Combined with the lower bound from Step 111, this gives the two-sided bound
`-log(βJD) ≤ latticeMass ≤ -log(tanh(βJ))` in the high-temperature regime.

Proof: for each `α : NNReal` with `HasExponentialDecay` at rate `α` and witness `C`, we show
`α ≤ -log(tanh(βJ))` by contradiction. Set `ε := log(tanh(βJ)) + α > 0`. By Archimedean,
find `n₀ : ℕ` with `C < ε * n₀`. The axis point `r_n = (n₀,0,...,0)` satisfies
`dist(0, r_n) = n₀`. Step 114 gives `tanh(βJ)^n₀ ≤ twoPointFunction d p r_n = |truncated2|
≤ C * exp(-α * n₀)`. Rearranging: `exp(ε * n₀) ≤ C`. But `exp(ε * n₀) ≥ ε * n₀ + 1 > C`.
Contradiction.

Reference: Glimm–Jaffe §17.5 pp. 304–306 (2nd ed.). -/
theorem latticeMass_le_neg_log_tanh_betaJ
    {d : ℕ} (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
      ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J))) := by
  have htanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hβ hJ)) (Real.cosh_pos _)
  unfold latticeMass
  apply sSup_le
  rintro b ⟨α, hα_dec, rfl⟩
  change (↑α : ENNReal) ≤ ENNReal.ofReal (-Real.log (Real.tanh (β * J)))
  obtain ⟨C, hC, hbound⟩ := hα_dec
  suffices h_le : (α : ℝ) ≤ -Real.log (Real.tanh (β * J)) by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h_le
  by_contra h_alpha_gt
  simp only [not_le] at h_alpha_gt
  set ε := Real.log (Real.tanh (β * J)) + (α : ℝ) with hε_def
  have hε_pos : 0 < ε := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (C / ε)
  have hn₀_ε : C < ε * ↑n₀ := by
    have h := (div_lt_iff₀ hε_pos).mp hn₀
    rwa [mul_comm (↑n₀ : ℝ) ε] at h
  have hn₀_pos : 0 < n₀ :=
    Nat.cast_pos.mp ((div_nonneg hC hε_pos.le).trans_lt hn₀)
  set r_n := fun i : Fin d => if i.val = 0 then (n₀ : ℤ) else 0
  have hr_ne : r_n ≠ 0 := by
    intro heq
    have h0 : (n₀ : ℤ) = 0 := by
      have := congr_fun heq ⟨0, hd⟩
      simp only [Pi.zero_apply, r_n, if_pos rfl] at this
      exact this
    exact absurd h0 (by exact_mod_cast hn₀_pos.ne')
  have hdist : latticeDistance d 0 r_n = n₀ := latticeDistance_coord_eq hd n₀
  have h_lb : Real.tanh (β * J) ^ n₀ ≤ twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r_n :=
    hdist ▸ twoPointFunction_ge_tanh_betaJ_pow_dist hJ.le hβ hr_ne
  have h_ub : twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) r_n ≤
      C * Real.exp (-(↑α : ℝ) * ↑n₀) := by
    have h' := hbound 0 r_n (Ne.symm hr_ne)
    simp only [truncated2Infinite_h_zero] at h'
    rw [abs_of_nonneg (correlationInfinite_nonneg_of_hβJ (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (mul_nonneg hβ.le hJ.le) {0, r_n}),
        ← twoPointFunction_apply, hdist] at h'
    exact h'
  have h_combined : Real.tanh (β * J) ^ n₀ ≤ C * Real.exp (-(↑α : ℝ) * ↑n₀) :=
    h_lb.trans h_ub
  have h_exp_le_C : Real.exp (ε * ↑n₀) ≤ C := by
    have key : Real.exp (ε * ↑n₀) =
        Real.tanh (β * J) ^ n₀ * Real.exp ((↑α : ℝ) * ↑n₀) := by
      rw [hε_def, add_mul, Real.exp_add,
          show Real.log (Real.tanh (β * J)) * ↑n₀ = ↑n₀ * Real.log (Real.tanh (β * J))
            from mul_comm _ _,
          ← Real.log_pow (Real.tanh (β * J)) n₀,
          Real.exp_log (pow_pos htanh_pos n₀)]
    rw [key]
    calc Real.tanh (β * J) ^ n₀ * Real.exp ((↑α : ℝ) * ↑n₀)
        ≤ C * Real.exp (-(↑α : ℝ) * ↑n₀) * Real.exp ((↑α : ℝ) * ↑n₀) :=
            mul_le_mul_of_nonneg_right h_combined (Real.exp_pos _).le
      _ = C := by
            rw [mul_assoc, ← Real.exp_add]
            have h0 : -(↑α : ℝ) * ↑n₀ + (↑α : ℝ) * ↑n₀ = 0 := by ring
            rw [h0, Real.exp_zero, mul_one]
  linarith [Real.add_one_le_exp (ε * ↑n₀)]

/-- **Lattice mass two-sided bound** (Step 153, GJ §17.5 pp. 304–306):
in the high-temperature regime (`d ≥ 1`, `0 < J`, `0 < β`, `βJ·2d < 1`):
`ENNReal.ofReal (-log(βJ·2d)) ≤ latticeMass ≤ ENNReal.ofReal (-log(tanh(βJ)))`.

Bundles `latticeMass_ge_neg_log_of_high_temp` (lower, Step 152) and
`latticeMass_le_neg_log_tanh_betaJ` (upper, Step 115) into one statement. -/
theorem latticeMass_two_sided_bound
    {d : ℕ} (hd : 0 < d) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    ENNReal.ofReal (-Real.log (β * J * ↑(2 * d))) ≤
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) ≤
    ENNReal.ofReal (-Real.log (Real.tanh (β * J))) :=
  ⟨latticeMass_ge_neg_log_of_high_temp hd (mul_pos hβ hJ) hlt,
   latticeMass_le_neg_log_tanh_betaJ hd hJ hβ⟩

/-! ## Step 127: Lebowitz–exponential product bound (GJ §17.5 PR N+2) -/

/-- Uniform upper bound on each factor under exponential decay.

Under `HasExponentialDecay` with constant `C` and rate `α`, each
`truncated2Infinite(i, z)` is bounded uniformly for ALL `z` (including `i = z`)
by `(C + 1) * exp(-α/2 * d(i, z))`.

At `i = z`: uses `truncated2Infinite_le_one` (≤ 1 ≤ C+1).
At `i ≠ z`: uses the decay bound `C * exp(-α*d) ≤ (C+1) * exp(-α/2 * d)` for
`d ≥ 0` (since `-α*d ≤ -α/2*d` and `C ≤ C+1`). -/
private lemma truncated2Infinite_le_hDecay_uniform
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ i j : Fin d → ℤ, i ≠ j →
        |Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ C * Real.exp (-α * (latticeDistance d i j : ℝ)))
    (i z : Fin d → ℤ) :
    Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) i z
    ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d i z : ℝ)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hnn : 0 ≤ Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) i z :=
    Ambient.truncated2Infinite_nonneg (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hf i z
  rcases eq_or_ne i z with rfl | hiz
  · -- Diagonal: truncated2(i,i) ≤ 1 ≤ (C+1)·1 = (C+1)·exp(-α/2·0)
    have hle1 := Ambient.truncated2Infinite_le_one (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf i i
    simp only [latticeDistance_self, Nat.cast_zero, mul_zero, Real.exp_zero]
    linarith
  · -- Off-diagonal: C·exp(-α·d) ≤ (C+1)·exp(-α/2·d)
    have habs := hbound i z hiz
    rw [abs_of_nonneg hnn] at habs
    have hdist_nn : (0 : ℝ) ≤ latticeDistance d i z := Nat.cast_nonneg _
    calc Ambient.truncated2Infinite _ _ _ i z
        ≤ C * Real.exp (-α * (latticeDistance d i z : ℝ)) := habs
      _ ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d i z : ℝ)) := by
            apply mul_le_mul (le_add_of_nonneg_right one_pos.le)
              (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (by linarith)

/-- **Summability of the truncated-2 product sum** under exponential decay (Step 127).

Under `HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩) α`, the sum
`∑_z truncated2Inf(x,z) · truncated2Inf(y,z)` is summable over `ℤ^d`.

Proof: both factors are nonneg (GKS-II) and uniformly bounded by `(C+1)·exp(-α/2·d)`;
the product is bounded by `(C+1)²·exp(-α/2·d(x,z))·exp(-α/2·d(y,z))`; this is
summable by `summable_exp_neg_dist` with rate `α/2`.

**Reference**: GJ §17.5 (applying Lemma 17.5.2 exponential decay). -/
theorem summable_truncated2Infinite_prod_of_hasExponentialDecay
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α : ℝ} (hα : 0 < α)
    (hdecay : HasExponentialDecay d (Ambient.cubicExhaustion d)
                (⟨J, 0, β⟩ : IsingParams ℝ) α)
    (x y : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ =>
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z *
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) y z) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hα2 : 0 < α / 2 := half_pos hα
  refine Summable.of_nonneg_of_le
    (fun z => mul_nonneg (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                            (Ambient.cubicExhaustion d) _ hf x z)
                         (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                            (Ambient.cubicExhaustion d) _ hf y z))
    (fun z => ?_)
    ((summable_exp_neg_dist hα2 d x).mul_left ((C + 1) ^ 2))
  have hx := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound x z
  have hy := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound y z
  have hnn_y := Ambient.truncated2Infinite_nonneg (latticeGraph d)
                  (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf y z
  calc Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
      ≤ (C + 1) * Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
        ((C + 1) * Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) :=
          mul_le_mul hx hy hnn_y (mul_nonneg (by linarith) (Real.exp_nonneg _))
    _ = (C + 1) ^ 2 *
        (Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
         Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) := by ring
    _ ≤ (C + 1) ^ 2 * Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_of_le_one_right (Real.exp_nonneg _)
                (Real.exp_le_one_iff.mpr (by
                  nlinarith [hα2.le, show (0:ℝ) ≤ latticeDistance d y z from Nat.cast_nonneg _]))

/-- **Upper bound on the truncated-2 product tsum** (Step 127).

Under `HasExponentialDecay d (cubicExhaustion d) (⟨J, 0, β⟩) α` with witness constant `C`,
the infinite sum satisfies:
```
∑_z truncated2Inf(x,z) · truncated2Inf(y,z) ≤
  (C+1)² · 2 · C(α/2, d) · exp(-α/4 · d(x,y))
```
where `C(α/2, d) = ∑_z exp(-α/2 · d(0,z))`.

The uniform factor `C+1` absorbs both the off-diagonal decay `C·exp(-α·d)` and the
diagonal bound `≤ 1` (GKS-II), avoiding case analysis. The rate `α/4` comes from
applying `lattice_exp_sum_conv_le` with rate `α/2`.

**Reference**: GJ §17.5, Lemma 17.5.2. -/
theorem tsum_truncated2Infinite_prod_le
    {d : ℕ} {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ i j : Fin d → ℤ, i ≠ j →
        |Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) i j|
        ≤ C * Real.exp (-α * (latticeDistance d i j : ℝ)))
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z *
        Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) y z
    ≤ (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
          Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
        Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  have hα2 : 0 < α / 2 := half_pos hα
  -- Uniform pointwise bound using C+1
  have hle_prod : ∀ z : Fin d → ℤ,
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z
      ≤ (C + 1) ^ 2 * (Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
                        Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) := by
    intro z
    have hx := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound x z
    have hy := truncated2Infinite_le_hDecay_uniform hJ hβ hα hC hbound y z
    have hnn_y := Ambient.truncated2Infinite_nonneg (latticeGraph d)
                    (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf y z
    calc Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
        ≤ (C + 1) * Real.exp (-(α / 2) * _) * ((C + 1) * Real.exp (-(α / 2) * _)) :=
            mul_le_mul hx hy hnn_y (mul_nonneg (by linarith) (Real.exp_nonneg _))
      _ = (C + 1) ^ 2 * (Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _)) := by ring
  -- Summability of the comparison
  have hsumm_conv : Summable (fun z : Fin d → ℤ =>
      Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
      Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (fun z => mul_le_of_le_one_right (Real.exp_nonneg _)
                  (Real.exp_le_one_iff.mpr (by
                    nlinarith [hα2.le,
                      show (0:ℝ) ≤ latticeDistance d y z from Nat.cast_nonneg _])))
      (summable_exp_neg_dist hα2 d x)
  have hprod_summable : Summable (fun z : Fin d → ℤ =>
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z *
      Ambient.truncated2Infinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) y z) :=
    Summable.of_nonneg_of_le
      (fun z => mul_nonneg (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                              (Ambient.cubicExhaustion d) _ hf x z)
                           (Ambient.truncated2Infinite_nonneg (latticeGraph d)
                              (Ambient.cubicExhaustion d) _ hf y z))
      hle_prod (hsumm_conv.mul_left _)
  -- Main calc
  calc ∑' z, Ambient.truncated2Infinite _ _ _ x z * Ambient.truncated2Infinite _ _ _ y z
      ≤ ∑' z, (C + 1) ^ 2 * (Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _)) :=
          hprod_summable.tsum_le_tsum hle_prod (hsumm_conv.mul_left _)
    _ = (C + 1) ^ 2 * ∑' z, Real.exp (-(α / 2) * _) * Real.exp (-(α / 2) * _) :=
          tsum_mul_left
    _ ≤ (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
            Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
          Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by
          have hconv := lattice_exp_sum_conv_le hα2 d x y
          calc (C + 1) ^ 2 * ∑' z : Fin d → ℤ,
                  Real.exp (-(α / 2) * (latticeDistance d x z : ℝ)) *
                  Real.exp (-(α / 2) * (latticeDistance d y z : ℝ))
              ≤ (C + 1) ^ 2 * (2 * (∑' z : Fin d → ℤ,
                    Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
                  Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left hconv (sq_nonneg _)
            _ = (C + 1) ^ 2 * (2 * ∑' z : Fin d → ℤ,
                    Real.exp (-(α / 2) * (latticeDistance d 0 z : ℝ))) *
                Real.exp (-(α / 2) * (latticeDistance d x y : ℝ) / 2) := by ring

/-! ## §17.1 Critical inverse temperature -/

/-- **Critical inverse temperature** for the d-dimensional Ising model on ℤ^d
with coupling `J` (no ferromagneticity required in the definition): the supremum (in `ENNReal`)
of all inverse temperatures `β ≥ 0` for which the lattice mass
`latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩` is strictly positive.

For β strictly below this threshold (and J > 0 ferromagnetic) the model is in the
high-temperature phase with exponential decay. For β strictly above the threshold the mass
equals 0 (see `latticeMass_eq_zero_of_criticalInverseTemp_lt`); for fixed J > 0 and
sufficiently large β, a genuine two-phase region appears in d ≥ 2 (Peierls, §5.4).

**GJ §17.1 analogy**: Glimm–Jaffe define the critical coupling `σ_c` as the infimum of
σ (mass² parameter) for which the φ⁴ theory has a unique phase with exponential decay.
Our `criticalInverseTemp d J` is the lattice Ising analog: because higher β = lower
temperature = stronger interaction, the critical point is a supremum in β rather than an
infimum in σ. -/
noncomputable def criticalInverseTemp (d : ℕ) (J : ℝ) : ENNReal :=
  sSup (ENNReal.ofReal ''
    { β : ℝ | 0 ≤ β ∧ 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) })

/-- The defining set for `criticalInverseTemp` is non-empty: at `β = 0` the lattice mass
equals `⊤ > 0` (see `latticeMass_top_of_beta_zero`), so `0 ∈ {β | 0 ≤ β ∧ mass > 0}`. -/
theorem criticalInverseTemp_set_nonempty (d : ℕ) (J : ℝ) :
    (ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧
        0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) }).Nonempty :=
  ⟨ENNReal.ofReal 0, 0,
    ⟨le_refl 0, by simp [latticeMass_top_of_beta_zero]⟩, rfl⟩

/-- The critical inverse temperature is nonneg; trivially in `ENNReal`. -/
theorem criticalInverseTemp_nonneg (d : ℕ) (J : ℝ) : 0 ≤ criticalInverseTemp d J :=
  zero_le _

/-- **High-temperature lower bound on `criticalInverseTemp`** (GJ §17.1):
for `d ≥ 1` and `J > 0`, the critical inverse temperature satisfies
`β_c ≥ ENNReal.ofReal (1 / (2 * J * 2d)) > 0`.

Proof: the midpoint `β₀ := 1 / (2 * J * 2d)` satisfies `β₀ * J > 0` and
`β₀ * J * 2d = 1/2 < 1`, so `latticeMass_pos_of_high_temp` gives `mass > 0` at `β₀`.
Hence `β₀` lies in the defining set and `criticalInverseTemp ≥ ENNReal.ofReal β₀ > 0`. -/
theorem criticalInverseTemp_ge_ofReal_high_temp
    {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J) :
    ENNReal.ofReal (1 / (2 * J * ↑(2 * d))) ≤ criticalInverseTemp d J := by
  have h2d_pos : (0 : ℝ) < ↑(2 * d) := by exact_mod_cast Nat.mul_pos two_pos (by omega)
  have hβ_pos : (0 : ℝ) < 1 / (2 * J * ↑(2 * d)) := by positivity
  have hβJ : 0 < 1 / (2 * J * ↑(2 * d)) * J := mul_pos hβ_pos hJ
  have hβJd : 1 / (2 * J * ↑(2 * d)) * J * ↑(2 * d) < 1 := by
    have h2Jd_pos : (0 : ℝ) < 2 * J * ↑(2 * d) := by positivity
    rw [show (1 : ℝ) / (2 * J * ↑(2 * d)) * J * ↑(2 * d) =
        J * ↑(2 * d) / (2 * J * ↑(2 * d)) from by ring,
      div_lt_one h2Jd_pos]
    linarith [mul_pos hJ h2d_pos]
  have hmass : 0 < latticeMass d (cubicExhaustion d)
      (⟨J, 0, 1 / (2 * J * ↑(2 * d))⟩ : IsingParams ℝ) :=
    latticeMass_pos_of_high_temp hβJ hβJd
  have hmem : (1 / (2 * J * ↑(2 * d)) : ℝ) ∈
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨le_of_lt hβ_pos, hmass⟩
  calc ENNReal.ofReal (1 / (2 * J * ↑(2 * d)))
      ≤ sSup (ENNReal.ofReal '' { β : ℝ | 0 ≤ β ∧
          0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) }) :=
        le_sSup ⟨1 / (2 * J * ↑(2 * d)), hmem, rfl⟩
    _ = criticalInverseTemp d J := rfl

/-- The critical inverse temperature is strictly positive for `d ≥ 1` and `J > 0`:
the high-temperature bound `β_c ≥ 1/(2J·2d) > 0` guarantees positivity. -/
theorem criticalInverseTemp_pos {d : ℕ} (hd : 1 ≤ d) {J : ℝ} (hJ : 0 < J) :
    0 < criticalInverseTemp d J :=
  (ENNReal.ofReal_pos.mpr (by positivity)).trans_le
    (criticalInverseTemp_ge_ofReal_high_temp hd hJ)

/-- **Critical inverse temperature is antitone in the coupling J** (GJ §17.1 Cor 17.1.2 analog):
for `0 ≤ J₁ ≤ J₂`, the critical inverse temperature satisfies `β_c(J₂) ≤ β_c(J₁)`.

Physics: stronger coupling (larger J) → smaller lattice mass at fixed β (longer correlation
length) → phase transition occurs at higher temperature (= smaller β_c, since β_c = 1/T_c
and larger T_c means smaller β_c). Proof: `latticeMass_antitone_J` gives
`latticeMass(J₁, β) ≥ latticeMass(J₂, β)` for β > 0, so the high-temperature set for J₁
contains the high-temperature set for J₂, hence sSup J₁ ≥ sSup J₂.

**GJ §17.1 monotonicity analog**: Cor 17.1.2 states that the mass m(σ) is monotone
increasing in σ (larger σ = weaker coupling = larger mass). Here J plays the role of
-σ, so increasing J decreases the mass at fixed β, lowering β_c. -/
theorem criticalInverseTemp_antitone_J
    {d : ℕ} {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₁₂ : J₁ ≤ J₂) :
    criticalInverseTemp d J₂ ≤ criticalInverseTemp d J₁ := by
  unfold criticalInverseTemp
  apply sSup_le_sSup
  rintro x ⟨β, ⟨hβ_nn, hmass_pos⟩, rfl⟩
  refine ⟨β, ⟨hβ_nn, ?_⟩, rfl⟩
  rcases eq_or_lt_of_le hβ_nn with rfl | hβ_pos
  · simp [latticeMass_top_of_beta_zero]
  · exact lt_of_lt_of_le hmass_pos
      (latticeMass_antitone_J (cubicExhaustion d) hJ₁ hJ₁₂ hβ_pos)

/-! ## §17.1 Critical inverse temperature — characterization -/

/-- **Lower bound on `criticalInverseTemp` from positive mass** (GJ §17.1):
if `latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ > 0` for some `β ≥ 0`, then
`ENNReal.ofReal β ≤ criticalInverseTemp d J`.

Proof: `β` is in the defining set of `criticalInverseTemp`, so `ENNReal.ofReal β` is
in the image set, and `le_sSup` gives the bound. -/
theorem criticalInverseTemp_ge_ofReal_of_latticeMass_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ENNReal.ofReal β ≤ criticalInverseTemp d J :=
  le_sSup ⟨β, ⟨hβ, h⟩, rfl⟩

/-- **Mass vanishes above the critical inverse temperature** (GJ §17.1):
if `criticalInverseTemp d J < ENNReal.ofReal β` (and `β ≥ 0`), then
`latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ = 0`.

This is the characterization: for β strictly above the critical threshold, the
high-temperature exponential-decay regime ends and mass vanishes (within the ENNReal lattice).
Proof: contrapositive of `criticalInverseTemp_ge_ofReal_of_latticeMass_pos`. -/
theorem latticeMass_eq_zero_of_criticalInverseTemp_lt
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : criticalInverseTemp d J < ENNReal.ofReal β) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 := by
  by_contra hm
  exact absurd h (not_lt.mpr
    (criticalInverseTemp_ge_ofReal_of_latticeMass_pos hβ (lt_of_le_of_ne (zero_le _) (Ne.symm hm))))

/-- **Positive mass below the critical inverse temperature** (GJ §17.1):
for ferromagnetic `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`,
the lattice mass is strictly positive.

Together with `latticeMass_eq_zero_of_criticalInverseTemp_lt` and
`criticalInverseTemp_ge_ofReal_of_latticeMass_pos`, this gives a near-complete picture:
`ENNReal.ofReal β < β_c → mass > 0 → ENNReal.ofReal β ≤ β_c`
(where `β_c = criticalInverseTemp d J`).
The boundary case `ENNReal.ofReal β = criticalInverseTemp d J` remains undetermined.

**GJ §17.1 context**: for σ < σ_c (= β < β_c in the Ising analog), the theory has
exponential decay of correlations; this is the defining property of the critical coupling.

Proof: by contradiction — if mass(J, β) = 0, then for all β' ≥ β (and β > 0), the
antitonicity `latticeMass_antitone_beta` gives mass(J, β') ≤ mass(J, β) = 0. Hence the
defining set ⊆ `[0, β)`, so `criticalInverseTemp ≤ ENNReal.ofReal β`, contradicting
`ENNReal.ofReal β < criticalInverseTemp`. The β = 0 case is vacuous since mass(J, 0) = ⊤. -/
theorem latticeMass_pos_of_lt_criticalInverseTemp
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  by_contra hm
  rw [not_lt] at hm
  have hm_zero : latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 :=
    le_antisymm hm (latticeMass_nonneg _ _ _)
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp [latticeMass_top_of_beta_zero] at hm_zero
  · have h_bound : criticalInverseTemp d J ≤ ENNReal.ofReal β := by
      unfold criticalInverseTemp
      apply sSup_le
      intro b hb
      rw [Set.mem_image] at hb
      obtain ⟨γ, ⟨hγ_nn, hmass_γ⟩, hγ_eq⟩ := hb
      rw [← hγ_eq]
      apply ENNReal.ofReal_le_ofReal
      by_cases h_le : γ ≤ β
      · exact h_le
      · rw [not_le] at h_le
        have hmono := latticeMass_antitone_beta (cubicExhaustion d) hJ hβ_pos h_le.le
        rw [hm_zero] at hmono
        exact absurd hmass_γ (not_lt.mpr hmono)
    exact absurd h (not_lt.mpr h_bound)

/-! ## §17.1 Cluster property below criticalInverseTemp (Step 146) -/

/-- **Extract positive decay rate from positive lattice mass** (GJ §17.1):
if `latticeMass d Λ p > 0`, there exists `α : NNReal` with `0 < (α : ℝ)` and
`HasExponentialDecay d Λ p (α : ℝ)`.

Proof: by `lt_sSup_iff`, a positive supremum of the image set contains some
element `(α : ENNReal) > 0`; coercing via `ENNReal.coe_pos` and
`NNReal.coe_pos` yields a positive real decay rate.

**GJ §17.1 context**: the positivity of the lattice mass (= inverse correlation
length) directly produces an exponential decay witness, connecting the abstract
`latticeMass` definition to the `HasExponentialDecay` predicate. -/
theorem HasExponentialDecay_of_latticeMass_pos
    {d : ℕ} {Λ : Ambient.Exhaustion (Fin d → ℤ)} {p : IsingParams ℝ}
    (h : 0 < latticeMass d Λ p) :
    ∃ α : NNReal, 0 < (α : ℝ) ∧ HasExponentialDecay d Λ p (α : ℝ) := by
  unfold latticeMass at h
  rw [lt_sSup_iff] at h
  obtain ⟨y, hy_mem, hy_pos⟩ := h
  rw [Set.mem_image] at hy_mem
  obtain ⟨α, hα_decay, hα_eq⟩ := hy_mem
  rw [← hα_eq] at hy_pos
  exact ⟨α, NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hy_pos), hα_decay⟩

/-- **Transfer `HasExponentialDecay` across exhaustions** (private helper):
for ferromagnetic `p`, if `HasExponentialDecay d Λ p α` holds for some
exhaustion `Λ`, then it holds for any other exhaustion `Λ'`.

Proof: the truncated 2-point function is exhaustion-independent for ferromagnetic
parameters (`truncated2Infinite_indep_exhaustion`), so the bound transfers directly
from `Λ` to `Λ'` with the same constant `C` and rate `α`. -/
private lemma HasExponentialDecay_transfer_exhaustion
    {d : ℕ} (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} {α : ℝ}
    (hf : Ferromagnetic p)
    (h : HasExponentialDecay d Λ p α) :
    HasExponentialDecay d Λ' p α := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun i j hij => ?_⟩
  rw [truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ' Λ p hf i j]
  exact hbound i j hij

/-- **Cluster property holds below the critical inverse temperature** (GJ §17.1):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the
cluster property holds for any exhaustion `Λ`:
```
clusterProperty (latticeGraph d) Λ ⟨J, 0, β⟩.
```

**Physics**: the hypothesis `β < β_c` is the **high-temperature** regime
(equivalently, above the critical temperature `T_c = 1/β_c`). In this regime,
the connected 2-point function decays exponentially: for all `i, j`,
`|⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩|` decays to zero as `|i - j| → ∞`. This is the
GJ §17.1 high-temperature clustering consequence for the Ising model analog.

**Proof strategy**:
* `β = 0`: `clusterProperty_latticeGraph_beta_zero` (trivial slice).
* `β > 0`: use `latticeMass_pos_of_lt_criticalInverseTemp` to get `m > 0`,
  extract a positive rate `α` via `HasExponentialDecay_of_latticeMass_pos`,
  transfer the decay from `cubicExhaustion d` to `Λ` via
  `HasExponentialDecay_transfer_exhaustion` (uses `Ferromagnetic`), and
  conclude by `clusterProperty_latticeGraph_of_HasExponentialDecay`. -/
theorem clusterProperty_latticeGraph_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    clusterProperty (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · exact clusterProperty_latticeGraph_beta_zero d Λ J 0
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
      ⟨hJ, le_refl _, hβ_pos⟩
    have hα_decay' : HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (α : ℝ) :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    exact clusterProperty_latticeGraph_of_HasExponentialDecay d Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hα_pos hα_decay'

/-- **Summability of truncated 2-point below critical inverse temperature** (GJ §17.1/§17.5):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`, the truncated
2-point function is summable:
`Summable (fun j => truncated2Infinite (latticeGraph d) Λ ⟨J, 0, β⟩ i j)`.

This extends `truncated2Infinite_summable_of_high_temp` (βJD < 1 case, PR #903) to the
full below-β_c regime, giving a per-site finite-susceptibility result for all high-temperature
couplings (not just the Simon-Lieb high-temperature range).

**Proof**: β = 0 gives `U_2 = 0` (summable trivially). For β > 0: `latticeMass > 0`
(via `latticeMass_pos_of_lt_criticalInverseTemp`) → extract `α > 0` and
`HasExponentialDecay` (via `HasExponentialDecay_of_latticeMass_pos`) → transfer to `Λ`
(via `HasExponentialDecay_transfer_exhaustion`) → `|U_2(i,j)| ≤ C·exp(-α·d(i,j))` for
`i ≠ j` and `U_2(i,i) = 0` (Z₂ symmetry) → `summable_exp_neg_dist` + nonneg bound
→ `Summable.of_nonneg_of_le`. -/
theorem truncated2Infinite_summable_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    Summable (fun j : Fin d → ℤ =>
      truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i j) := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp only [truncated2Infinite_beta_zero (IsingModel.latticeGraph d) Λ J 0]
    exact summable_zero
  · have hm_pos : 0 < latticeMass d (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) :=
      latticeMass_pos_of_lt_criticalInverseTemp hβ_pos.le hJ h
    obtain ⟨α, hα_pos, hα_decay⟩ := HasExponentialDecay_of_latticeMass_pos hm_pos
    have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl _, hβ_pos⟩
    obtain ⟨C, hC, hbound⟩ :=
      HasExponentialDecay_transfer_exhaustion (cubicExhaustion d) Λ hf hα_decay
    apply Summable.of_nonneg_of_le
        (fun j => truncated2Infinite_nonneg (IsingModel.latticeGraph d) Λ _ hf i j)
        (fun j => ?_)
        ((summable_exp_neg_dist hα_pos d i).mul_left C)
    by_cases hij : i = j
    · subst hij
      rw [truncated2Infinite_h_zero (IsingModel.latticeGraph d) Λ J β i i]
      simp only [Finset.pair_eq_singleton]
      rw [Ambient.correlationInfinite_h_zero (IsingModel.latticeGraph d) Λ J β {i} (by simp)]
      exact mul_nonneg hC (Real.exp_nonneg _)
    · exact le_trans (le_abs_self _) (hbound i j hij)

/-! ## §17.1 d = 0 special case -/

/-- **Vacuous HasExponentialDecay in dimension zero**: for `d = 0`, the lattice
`Fin 0 → ℤ` is a singleton, so there are no distinct pairs `(i, j)`, and
`HasExponentialDecay 0 Λ p α` holds for every `Λ`, `p`, and `α`. -/
private lemma HasExponentialDecay_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) (α : ℝ) :
    HasExponentialDecay 0 Λ p α :=
  ⟨0, le_refl _, fun _i _j hij =>
    absurd (funext (fun x => Fin.elim0 x)) hij⟩

/-- **Lattice mass is `⊤` in dimension zero**: the set of valid decay rates is all of
`NNReal` (vacuous condition), so `latticeMass = sSup (NNReal → ENNReal) = ⊤`. -/
private lemma latticeMass_eq_top_of_dim_zero
    (Λ : Ambient.Exhaustion (Fin 0 → ℤ)) (p : IsingParams ℝ) :
    latticeMass 0 Λ p = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay 0 Λ p (α : ℝ)} :=
    ⟨α, HasExponentialDecay_dim_zero Λ p (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  exact absurd hα_le_b (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-- **Critical inverse temperature is `⊤` in dimension zero** (GJ §17.1):
for `d = 0` (single-site model, no neighbors), the lattice mass is always `⊤ > 0`,
so all `β ≥ 0` are in the high-temperature set and `criticalInverseTemp 0 J = ⊤`.

Physics: a zero-dimensional Ising model has no ferromagnetic interactions and no
phase transition at any temperature; the "critical temperature" is infinite (β_c = ⊤). -/
theorem criticalInverseTemp_eq_top_of_dim_zero (J : ℝ) :
    criticalInverseTemp 0 J = ⊤ := by
  unfold criticalInverseTemp
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  set β₀ : NNReal := b.toNNReal + 1
  have hmass_pos : 0 < latticeMass 0 (cubicExhaustion 0)
      (⟨J, 0, (β₀ : ℝ)⟩ : IsingParams ℝ) := by
    rw [latticeMass_eq_top_of_dim_zero]
    simp
  have hmem : ENNReal.ofReal (β₀ : ℝ) ∈ ENNReal.ofReal ''
      { β : ℝ | 0 ≤ β ∧ 0 < latticeMass 0 (cubicExhaustion 0)
          (⟨J, 0, β⟩ : IsingParams ℝ) } :=
    ⟨(β₀ : ℝ), ⟨NNReal.coe_nonneg _, hmass_pos⟩, rfl⟩
  have hle : ENNReal.ofReal (β₀ : ℝ) ≤ b := hb hmem
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b := ENNReal.coe_toNNReal hb_ne_top
  have hβ₀_eq : ENNReal.ofReal (β₀ : ℝ) = b + 1 := by
    simp only [β₀, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hβ₀_eq] at hle
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hb_ne_top one_ne_zero))

/-! ## §17.1 J = 0 special case -/

/-- **Critical inverse temperature is `⊤` when `J = 0`** (GJ §17.1):
for zero coupling constant, `latticeMass = ⊤` for every `β ≥ 0` (either from
`latticeMass_top_of_beta_zero` at `β = 0`, or from `latticeMass_top_of_J_zero` at `β > 0`),
so the defining set is all of `[0,∞)` and `criticalInverseTemp d 0 = ⊤`.

Physics: with no coupling between sites, no phase transition occurs at any finite inverse
temperature (β_c = ⊤ means T_c = 0). This is the J = 0 companion of
`criticalInverseTemp_eq_top_of_dim_zero`. -/
theorem criticalInverseTemp_eq_top_of_J_zero (d : ℕ) :
    criticalInverseTemp d 0 = ⊤ := by
  apply le_antisymm le_top
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  rw [← ENNReal.ofReal_natCast n]
  apply criticalInverseTemp_ge_ofReal_of_latticeMass_pos (Nat.cast_nonneg n)
  rcases n with _ | n
  · rw [Nat.cast_zero, latticeMass_top_of_beta_zero]; exact ENNReal.zero_lt_top
  · have hf : Ferromagnetic (⟨(0 : ℝ), (0 : ℝ), (↑(n + 1) : ℝ)⟩ : IsingParams ℝ) :=
      ⟨le_refl _, le_refl _, by positivity⟩
    rw [latticeMass_top_of_J_zero d (cubicExhaustion d) 0 _ hf]
    exact ENNReal.zero_lt_top

/-! ## §17.1 Finite susceptibility below critical inverse temperature (Step 149) -/

/-- **Susceptibility bounded above in the high-temperature regime** (GJ §17.1, ℤ^d):
for `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J` (high temperature,
i.e., above the critical temperature `T_c = 1/β_c`),
`susceptibilityInfinite (latticeGraph d) Λ ⟨J,0,β⟩ i`
`  ≤ ∑' j, truncated2Infinite (latticeGraph d) Λ ⟨J,0,β⟩ i j`.

Combines `susceptibilityInfinite_le_tsum_truncated2Infinite` (Step 148, `HighTemp.lean`)
with `truncated2Infinite_summable_of_lt_criticalInverseTemp` (Step 147) to give a concrete
finite upper bound on the susceptibility in the high-temperature regime.

**Physics**: the quantity `∑' j, truncated2Infinite ... i j` (the tsum of the Ursell
2-point function) provides a finite upper bound on the magnetic susceptibility,
a hallmark of the paramagnetic (disordered) phase (β < β_c = criticalInverseTemp).
GJ §17.1 motivates this finiteness as the defining property of exponential clustering. -/
theorem susceptibilityInfinite_latticeGraph_le_tsum_of_lt_criticalInverseTemp
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J)
    (i : Fin d → ℤ) :
    susceptibilityInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      ≤ ∑' j : Fin d → ℤ,
          truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) i j := by
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · -- β = 0: susceptibilityInfinite = 0 and ∑' = 0
    simp only [susceptibilityInfinite_eq_ciSup]
    apply ciSup_le; intro n
    simp only [susceptibilityAlongExhaustion]
    split_ifs with hi
    · rw [susceptibilityΛ_apply, susceptibility_apply]
      simp only [truncated2_beta_zero, Finset.sum_const_zero]
      exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
    · exact tsum_nonneg (fun j => by rw [truncated2Infinite_beta_zero])
  · exact susceptibilityInfinite_le_tsum_truncated2Infinite (IsingModel.latticeGraph d) Λ
        ⟨hJ, le_refl _, hβ_pos⟩ i
        (truncated2Infinite_summable_of_lt_criticalInverseTemp Λ hβ_pos.le hJ h i)

/-- **β-derivative bound for two-point function on ℤ^d** (Step 157, GJ §17.5):
For the induced lattice graph on any finite Λ ⊆ ℤ^d, vertices r ≠ s in ↑Λ,
the β-derivative of `correlation G ⟨J,0,β'⟩ {r,s}` is bounded by the Lebowitz sum
plus the uniform constant `J * 4d`.

Combines `correlation_beta_deriv_le_lebowitz_tight` (Step 154) with
`incidentEdgesFinset_inducedLatticeGraph_card_le` (Step 155): the incident-edge
term `J * |{e: r∈e ∨ s∈e}|` is at most `J * 4d`, uniform in |Λ|.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem inducedLatticeGraph_beta_deriv_le
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) (hrs : r ≠ s) :
    ∃ dval : ℝ,
      HasDerivAt (fun β' => IsingModel.correlation
          (inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β'⟩ : IsingParams ℝ) {r, s}) dval β ∧
      dval ≤ J * ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
            Sym2.lift ⟨fun u v =>
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
                IsingModel.correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
                  (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
              fun u v => by ring⟩ e
        + J * (4 * ↑d) := by
  set G := inducedGraph (IsingModel.latticeGraph d) Λ
  obtain ⟨dval, hd, hbound⟩ :=
    IsingModel.correlation_beta_deriv_le_lebowitz_tight G J β hJ hβ r s hrs
  refine ⟨dval, hd, ?_⟩
  have h_cast : (↑(G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card : ℝ) ≤ 4 * ↑d := by
    exact_mod_cast incidentEdgesFinset_inducedLatticeGraph_card_le d Λ r s
  linarith [mul_le_mul_of_nonneg_left h_cast hJ]

/-- **Bridge: finite-vol correlation ≤ ∞-vol correlation** (Step 158, GJ §17.5):
For any exhaustion Λ of ℤ^d, stage n, and vertices r, s : ↑(Λ.volume n),
the induced-graph correlation is bounded above by the infinite-volume correlation:
```
correlation (inducedGraph (latticeGraph d) Λ_n) ⟨J, 0, β⟩ {r, s}
  ≤ correlationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ {r.val, s.val}
```

Proof: `correlation G_n p {r,s} = correlationAlongExhaustion G Λ p {r.val,s.val} n`
(by unfolding the exhaustion definition and showing `liftFinset {r.val,s.val} h = {r,s}`)
then apply `correlationAlongExhaustion_le_correlationInfinite`.

Used to bound the Lebowitz sum from Step 157 by the ∞-vol susceptibility.

Reference: Glimm–Jaffe §17.5. -/
theorem correlation_inducedLatticeGraph_le_correlationInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (n : ℕ) (r s : ↑(Λ.volume n)) :
    IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      ≤ Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} := by
  have h_sub : {r.val, s.val} ⊆ Λ.volume n :=
    Finset.insert_subset r.2 (Finset.singleton_subset_iff.mpr s.2)
  have heq : IsingModel.correlation
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (⟨J, 0, β⟩ : IsingParams ℝ) {r, s}
      = Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {r.val, s.val} n := by
    rw [Ambient.correlationAlongExhaustion_of_subset _ _ _ h_sub, correlationΛ_apply]
    congr 1
    ext x
    simp only [Ambient.mem_liftFinset, Finset.mem_insert, Finset.mem_singleton,
               Subtype.ext_iff]
  rw [heq]
  exact Ambient.correlationAlongExhaustion_le_correlationInfinite _ _ _ _ _


/-! ## Step 160: Lebowitz sum ≤ product of correlation sums (GJ §17.5) -/

/-- **Dart injection bound** (Step 160 helper): for non-negative `f g : V → ℝ`,
`∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u, f u) * (∑ v, g v)`.

Proof: the dart-to-pair map `d ↦ (d.fst, d.snd)` injects into `V × V`; adding the
non-negative non-dart pairs to the sum only increases it. -/
private lemma sum_dart_le_mul_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℝ) (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    ∑ d : G.Dart, f d.fst * g d.snd ≤ (∑ u : V, f u) * (∑ v : V, g v) := by
  classical
  -- Expand RHS to double sum
  rw [Fintype.sum_mul_sum]
  -- Group LHS darts by fst vertex
  rw [(Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => Finset.mem_univ d.fst)
       (fun d => f d.fst * g d.snd)).symm]
  apply Finset.sum_le_sum
  intro u _
  -- Replace f d.fst by f u (using filter condition d.fst = u), then factor
  have h1 : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f d.fst * g d.snd
      = ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), f u * g d.snd :=
    Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2])
  rw [h1, ← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hf u)
  -- Bound ∑_{d: d.fst=u} g(d.snd) ≤ ∑_v g v via image
  have hinj : ∀ d₁ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      ∀ d₂ ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u),
      d₁.snd = d₂.snd → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h
    exact SimpleGraph.Dart.ext d₁ d₂ (Prod.ext
      ((Finset.mem_filter.mp hd₁).2.trans (Finset.mem_filter.mp hd₂).2.symm) h)
  calc ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), g d.snd
      = ∑ v ∈ (Finset.univ.filter (fun d : G.Dart => d.fst = u)).image (fun d => d.snd), g v := by
          rw [← Finset.sum_image hinj]
      _ ≤ ∑ v : V, g v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v _; exact Finset.mem_univ v
          · intro v _ _; exact hg v

/-- **Lebowitz sum bounded by product of correlation sums** (Step 160, GJ §17.5):
For the induced ℤ^d lattice graph on `Λ`,
```
∑_{e ∈ E(G)} (corr(r,u)·corr(s,v) + corr(r,v)·corr(s,u))
  ≤ (∑_j corr(r,j)) · (∑_j corr(s,j))
```

Proof: apply the dart product sum identity (`sum_edgeFinset_sym2_lift_prod_eq_sum_dart`),
then bound the dart sum by the full Cartesian product via the injectivity of
`d ↦ (d.fst, d.snd)` and GKS non-negativity.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_corr_sum_mul
    {d : ℕ} (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (r s : ↑Λ) :
    let G := inducedGraph (IsingModel.latticeGraph d) Λ
    let p := (⟨J, 0, β⟩ : IsingParams ℝ)
    ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation G p {r, u} * IsingModel.correlation G p {s, v} +
            IsingModel.correlation G p {r, v} * IsingModel.correlation G p {s, u},
            fun u v => by ring⟩ e
    ≤ (∑ j : ↑Λ, IsingModel.correlation G p {r, j}) *
      (∑ j : ↑Λ, IsingModel.correlation G p {s, j}) := by
  intro G p
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  have hcorr_nn : ∀ (x y : ↑Λ), 0 ≤ IsingModel.correlation G p {x, y} :=
    fun x y => gks_first G p hf _
  rw [SimpleGraph.sum_edgeFinset_sym2_lift_prod_eq_sum_dart]
  exact sum_dart_le_mul_sum G
    (fun u => IsingModel.correlation G p {r, u})
    (fun v => IsingModel.correlation G p {s, v})
    (fun u => hcorr_nn r u)
    (fun v => hcorr_nn s v)

/-- **Lebowitz sum bounded by susceptibilityAlongExhaustion product** (Step 161, GJ §17.5):
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityAlongExhaustion_n(r) · susceptibilityAlongExhaustion_n(s)`.

Proof: apply Step 160 + identify `∑_j corr_n(r,j) = susceptibilityAlongExhaustion_n(r.val)`
via `susceptibility_h_zero` + `susceptibilityAlongExhaustion_of_mem`.

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susc_along
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n)) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val n *
      susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val n := by
  classical
  set G := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n) with hG
  -- Identify ∑_j corr_n(r,j) = susceptibilityAlongExhaustion n r.val via h=0
  have hsusc_r : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {r, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ r.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  have hsusc_s : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      = ∑ j : ↑(Λ.volume n), IsingModel.correlation G (⟨J, 0, β⟩ : IsingParams ℝ) {s, j} := by
    rw [susceptibilityAlongExhaustion_of_mem _ _ _ s.2, susceptibilityΛ_apply,
        IsingModel.susceptibility_h_zero]
  rw [hsusc_r, hsusc_s]
  exact inducedLatticeGraph_leb_sum_le_corr_sum_mul (Λ.volume n) J β hJ hβ r s

/-- **Lebowitz sum bounded by susceptibilityInfinite product** (Step 162, GJ §17.5):
Under `BddAbove` for the susceptibility sequences,
`∑_{e∈E(G_n)} leb_n(e) ≤ susceptibilityInfinite_r · susceptibilityInfinite_s`.

Proof: Step 161 + `le_ciSup` (monotone convergence to the supremum).

Reference: Glimm–Jaffe §17.5. -/
theorem inducedLatticeGraph_leb_sum_le_susceptibilityInfinite
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (n : ℕ) (r s : ↑(Λ.volume n))
    (hbdd_r : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val m)))
    (hbdd_s : BddAbove (Set.range (fun m =>
        susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val m))) :
    ∑ e ∈ (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset,
        Sym2.lift ⟨fun u v =>
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, u} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, v} +
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {r, v} *
            IsingModel.correlation
                (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
                (⟨J, 0, β⟩ : IsingParams ℝ) {s, u},
            fun u v => by ring⟩ e
    ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) r.val *
      susceptibilityInfinite (IsingModel.latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  -- Step 161 bound
  have h161 := inducedLatticeGraph_leb_sum_le_susc_along Λ J β hJ hβ n r s
  -- susc_along_n ≤ susc_∞ via le_ciSup
  have hr : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) r.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_r n
  have hs : susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n
      ≤ susceptibilityInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) s.val := by
    rw [susceptibilityInfinite_eq_ciSup]; exact le_ciSup hbdd_s n
  -- Non-negativity
  have hr_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) r.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  have hs_nn : 0 ≤ susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) s.val n :=
    susceptibilityAlongExhaustion_nonneg _ _ _ hf _ _
  exact h161.trans (mul_le_mul hr hs hs_nn (hr_nn.trans hr))

end Ambient

end IsingModel
