import IsingModel.Conditioning.CorrelationClosed.GeneralField
import IsingModel.Conditioning.PlusOnePointRepresentation
import IsingModel.Conditioning.HighTempClosed.ClosedFormField
import IsingModel.ClusterExpansion.SourceGeneratingFunction
import IsingModel.ClusterExpansion.FieldMayerIdentity

/-!
# Honest general-boundary field two-point closed form (GJ §17.6.1, brick F4a)

This module collapses the still-open inner `σ`-sum of the already-proved
general-external-field subset expansion
`correlation_high_temp_expansion_general_h_subset_form`
(`GeneralField.lean`) into the honest closed form
\[
\langle\sigma_A\rangle_p
  = \frac{\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X\,\triangle\,A|}}
         {\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X|}},
\]
where `∂X = oddBoundary X` is the odd-degree (boundary) vertex set of the edge
subset `X` and `△` is the symmetric difference `symmDiff`.  It is the general-`h`,
general-observable generalization of the Friedli–Velenik high-temperature
two-point ratio (FV §3.7.3, eq. (3.46), p. 117): the hard boundary constraint
`∂X = A` is replaced by the soft field weight `tanh(βh)^{|∂X △ A|}`.  No
cluster-expansion / Kotecky–Preiss machinery is used; F4a is one purely finite
parity step.

The single new combinatorial fact is `oddFilter_add_indicator_eq_symmDiff`:
the `A`-shift of vertex parities is a single symmetric difference,
`{v : Odd(deg_X v + 1_{v∈A})} = ∂X △ A`.  Substituting the resulting closed form
of the inner `σ`-sum (`sum_spinProduct_edgeSpin_field_closed`) into numerator and
denominator, the common prefactor `2^{|ι|}·cosh(βh)^{|ι|}` cancels (it is
nonzero since `cosh > 0`, so no `Z ≠ 0` hypothesis is needed).  The denominator
is identified with the field polymer partition function `fieldPolymerZ`
(`fieldPolymerZ_eq_allSubgraphs_sum`).

References: Friedli–Velenik §3.7.3, eqs. (3.41)–(3.46), pp. 116–117, gives the
`h = 0` partition template. Exercise 5.8, p. 238, with its Appendix C solution,
p. 531, gives the exact field factor. The general-observable numerator is a
project extension.

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real
open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parity of an `A`-shifted `X`-degree is the symmetric difference** (brick F4a,
Helper 0): for any edge subset `X` and observable `A : Finset ι`,
\[
\{v : \mathrm{Odd}(\mathbf 1_{v\in A} + \deg_X v)\} = \partial X\,\triangle\,A,
\]
i.e. the vertices whose `A`-shifted `X`-degree is odd are exactly those in the
symmetric difference of the odd boundary `∂X = oddBoundary X` with `A`.  This is
the sole genuinely new combinatorial fact of F4a; it makes the observable `A`
and the geometric boundary `∂X` enter symmetrically.  The cardinality
`|∂X △ A|` need not be even (e.g. single-site `A`), so we never invoke evenness
of this exponent.  Proof: a parity case split on `v ∈ A` via `Nat.odd_add`. -/
private theorem oddFilter_add_indicator_eq_symmDiff
    (X : Finset (Sym2 ι)) (A : Finset ι) :
    (Finset.univ.filter
        (fun v => Odd ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)))
      = oddBoundary X ∆ A := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    oddBoundary]
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    simp only [hv, not_true, and_false, false_or, true_and]
    rw [add_comm, Nat.odd_add_one]
  · rw [if_neg hv]
    simp only [hv, not_false_iff, and_true, false_and, or_false, zero_add]

/-- **Closed form of the inner `σ`-sum** (brick F4a, Helper 1): for `X ⊆ E` and
any observable `A : Finset ι`,
\[
\sum_{\sigma}\sigma_A(\sigma)\Bigl(\prod_{e\in X}\sigma_e\Bigr)
   e^{\beta h\sum_i\sigma_i}
   = 2^{|\iota|}\cosh(\beta h)^{|\iota|}\,\tanh(\beta h)^{\,|\partial X\,\triangle\,A|}.
\]
Merges the two proved power decompositions of the spin factors
(`spinProduct_mul_prod_edgeSpin_eq_prod_pow`, exponent
`1_{v∈A} + deg_X v`) with the per-vertex field Fubini template
`sum_prod_toSign_pow_field` (at `a = βh`), then identifies the odd-parity vertex
set with `∂X △ A` via Helper 0 (`oddFilter_add_indicator_eq_symmDiff`).  The
field-observable counterpart of the parity collapse in
`partitionFunction_high_temp_expansion_field_closed`.

References: Friedli–Velenik §3.7.3, eq. (3.46), p. 117, gives the `h = 0`
observable template; Exercise 5.8, p. 238, with its Appendix C solution, p. 531,
gives the field factor. Arbitrary-observable parity is a project extension. -/
theorem sum_spinProduct_edgeSpin_field_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) {X : Finset (Sym2 ι)}
    (hX : X ∈ G.edgeFinset.powerset) :
    (∑ σ : Config ι,
        spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)))
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh (p.β * p.h) ^ Fintype.card ι *
          Real.tanh (p.β * p.h) ^ (oddBoundary X ∆ A).card := by
  -- The field exponential factorizes over vertices.
  have hexp : ∀ σ : Config ι,
      Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))
        = ∏ v : ι, Real.exp (p.β * p.h * ((σ v).toSign : ℝ)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [Spin.sign]
  -- Combine the observable and edge products into a per-vertex power with the
  -- `A`-shifted exponent, and absorb the field exponential per vertex.
  have hcombine : ∀ σ : Config ι,
      spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))
        = ∏ v : ι, (((σ v).toSign : ℝ) ^
              ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card)
            * Real.exp (p.β * p.h * ((σ v).toSign : ℝ))) := by
    intro σ
    rw [spinProduct_mul_prod_edgeSpin_eq_prod_pow G A X (Finset.mem_powerset.mp hX) σ,
        hexp σ, ← Finset.prod_mul_distrib]
  simp_rw [hcombine]
  rw [sum_prod_toSign_pow_field (p.β * p.h)
        (fun v => (if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card),
      oddFilter_add_indicator_eq_symmDiff X A]

/-- **Honest general-boundary field two-point closed form** (GJ §17.6.1, brick F4a):
for a finite `SimpleGraph G`, Ising parameter `p = (J, h, β)` and any observable
`A : Finset ι`,
\[
\langle\sigma_A\rangle_p
  = \frac{\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X\,\triangle\,A|}}
         {\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X|}}.
\]
The general external-field, general-observable closed form: the hard boundary
constraint `∂X = A` of the `h = 0` form (FV eq. (3.46)) is replaced by the soft
field weight `tanh(βh)^{|∂X △ A|}`.  For the pair `A = {i,j}` the term `X = ∅`
gives `∂X △ A = {i,j}`, so the isolated-source contribution `tanh(βh)^2`
survives in the numerator — the term whose omission broke the earlier
pair-only route appears here as a legitimate term of the honest closed form.

Proof: substitute `sum_spinProduct_edgeSpin_field_closed` into both numerator and
denominator of `correlation_high_temp_expansion_general_h_subset_form`; the common
prefactor `2^{|ι|}·cosh(βh)^{|ι|}` cancels via `mul_div_mul_left` (it is nonzero
since `cosh > 0`, so no `Z ≠ 0` hypothesis is needed).  At `h = 0` the field
factor is `1` on `∂X △ A = ∅` (i.e. `∂X = A`) and `0` otherwise, recovering the
even-subgraph boundary condition of the `h = 0` form.

References: Friedli–Velenik §3.7.3, eqs. (3.41)–(3.46), pp. 116–117, gives the
`h = 0` template; Exercise 5.8, p. 238, with its Appendix C solution, p. 531,
gives the exact field factor. This general-observable closed form is a project extension. -/
theorem correlation_high_temp_expansion_general_h_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlation G p A =
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          Real.tanh (p.β * p.h) ^ (oddBoundary X ∆ A).card) /
      (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          Real.tanh (p.β * p.h) ^ (oddBoundary X).card) := by
  -- The common cancellable prefactor `2^{|ι|}·cosh(βh)^{|ι|}` is nonzero.
  have hpref : (2 : ℝ) ^ Fintype.card ι * Real.cosh (p.β * p.h) ^ Fintype.card ι ≠ 0 :=
    (mul_pos (pow_pos two_pos _) (pow_pos (Real.cosh_pos _) _)).ne'
  -- Numerator: collapse each inner σ-sum and factor out the prefactor.
  have hnum :
      (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ι,
              spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)))
        = ((2 : ℝ) ^ Fintype.card ι * Real.cosh (p.β * p.h) ^ Fintype.card ι) *
          ∑ X ∈ G.edgeFinset.powerset,
            Real.tanh (p.β * p.J) ^ X.card *
              Real.tanh (p.β * p.h) ^ (oddBoundary X ∆ A).card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X hX => ?_)
    rw [sum_spinProduct_edgeSpin_field_closed G p A hX]
    ring
  -- Denominator: the `A = ∅` instance (`spinProduct ∅ = 1`, `∂X △ ∅ = ∂X`).
  have hden :
      (∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (p.β * p.J) ^ X.card *
            ∑ σ : Config ι,
              (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
              Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)))
        = ((2 : ℝ) ^ Fintype.card ι * Real.cosh (p.β * p.h) ^ Fintype.card ι) *
          ∑ X ∈ G.edgeFinset.powerset,
            Real.tanh (p.β * p.J) ^ X.card *
              Real.tanh (p.β * p.h) ^ (oddBoundary X).card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X hX => ?_)
    have hins : (∑ σ : Config ι,
          (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)))
        = ∑ σ : Config ι,
            spinProduct (∅ : Finset ι) σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) :=
      Finset.sum_congr rfl (fun σ _ => by rw [spinProduct_empty, one_mul])
    rw [hins, sum_spinProduct_edgeSpin_field_closed G p (∅ : Finset ι) hX,
        show oddBoundary X ∆ (∅ : Finset ι) = oddBoundary X from by simp]
    ring
  rw [correlation_high_temp_expansion_general_h_subset_form G p A, hnum, hden,
      mul_div_mul_left _ _ hpref]

/-- **Denominator of the honest closed form is the field polymer partition
function** (brick F4a): for Ising parameter `p = (J, h, β)`,
\[
\sum_{X\subseteq E}\tanh(\beta J)^{|X|}\,\tanh(\beta h)^{|\partial X|}
  = \texttt{fieldPolymerZ}\;G\;(\beta J)\;(\beta h).
\]
A definitional restatement of `fieldPolymerZ_eq_allSubgraphs_sum`
(`FieldMayerIdentity.lean`), since `oddBoundary X = univ.filter (Odd deg_X)`.
This identifies the denominator of
`correlation_high_temp_expansion_general_h_closed` with the field cluster-gas
partition function, the entry point to the complexified F4b/F5 bricks.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117, gives the `h = 0`
denominator template; Exercise 5.8, p. 238, with its Appendix C solution, p. 531,
gives the exact field denominator. This bridge is a project extension. -/
theorem correlation_high_temp_expansion_general_h_closed_denom_eq_fieldPolymerZ
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams ℝ) :
    (∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          Real.tanh (p.β * p.h) ^ (oddBoundary X).card)
      = fieldPolymerZ G (p.β * p.J) (p.β * p.h) := by
  rw [fieldPolymerZ_eq_allSubgraphs_sum]
  simp only [oddBoundary]

end IsingModel
